"""Instrument the existing offline evaluator without modifying policy decisions."""
import argparse
import hashlib
import json
import sys
import traceback
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--environments', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seeds', nargs='+', type=int, default=[0, 2, 4])
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    arc = args.source_root.resolve() / 'experiments/arc3'
    sys.path[:0] = [str(arc), str(arc / 'runtime')]
    from arc3.evaluate import run
    from explore_agent import ExploreAgent
    from vendor.explore.graph_explorer import GraphExplorer

    events, context, failures = [], {}, []
    original_init = ExploreAgent.__init__
    original_act = ExploreAgent.act
    original_reset = ExploreAgent.after_reset
    original_graph_reset = GraphExplorer.reset

    def serialize(value):
        return value.item() if hasattr(value, 'item') else sorted(value)

    def audit(graph):
        # Probe results and group membership must agree, and every successful
        # edge must occur exactly once in both adjacency directions.
        forward, reverse = set(), set()
        for node, info in graph._nodes.items():
            for idx, edge in enumerate(info.edge_data):
                memberships = [i for i, group in enumerate(info.group2remaining_candidate_ids) if idx in group]
                expected = [int(edge['group'])] if edge['result'] == 0 else []
                if memberships != expected:
                    raise RuntimeError(f'Candidate membership mismatch: {node}/{idx}')
                if edge['result'] == 1:
                    target = str(edge['target'])
                    if target not in graph._nodes:
                        raise RuntimeError(f'Missing target: {target}')
                    forward.add((node, idx, target))
                    reverse.add((target, idx, node))
                elif edge['target'] != '':
                    raise RuntimeError(f'Unsuccessful edge has a target: {node}/{idx}')
        if forward != {(n, i, t) for n, es in graph._G.items() for i, t in es}:
            raise RuntimeError('Forward adjacency mismatch')
        if reverse != {(n, i, t) for n, es in graph._G_rev.items() for i, t in es}:
            raise RuntimeError('Reverse adjacency mismatch')
        if graph._frontier != {n for n, info in graph._nodes.items() if info.has_open_group(graph.active_group)}:
            raise RuntimeError('Frontier membership mismatch')

    def graph_reset(self):
        self.diagnostic_epoch = getattr(self, 'diagnostic_epoch', -1) + 1
        return original_graph_reset(self)

    def initialize(self, *a, **kw):
        original_init(self, *a, **kw)
        graph = self.policy.graph_explorer
        original_record = graph.record_test

        def record(node, edge_idx, success, target_node=None, **kwargs):
            info = graph._nodes.get(node)
            edge = info.edge_data[edge_idx] if info is not None else None
            event = dict(context, epoch=graph.diagnostic_epoch, node=node, edge=int(edge_idx),
                         success=int(success), target=target_node, kwargs=kwargs,
                         before={k: edge[k].item() for k in edge.dtype.names} if edge is not None else None,
                         closed=info.closed if info else None,
                         groups=[sorted(g) for g in info.group2remaining_candidate_ids] if info else None,
                         active_group=graph.active_group, outgoing=sorted(graph._G.get(node, set())))
            events.append(event)
            try:
                result = original_record(node, edge_idx, success, target_node, **kwargs)
            except Exception:
                event['exception'] = traceback.format_exc()
                raise
            try:
                audit(graph)
            except RuntimeError as exc:
                failures.append(str(exc))
                event['exception'] = traceback.format_exc()
                raise
            event['audit'] = 'passed'
            return result
        graph.record_test = record

    def act(self):
        context.update(action_counter=self.policy.action_counter, level=self.current.levels,
                       level_up=self.policy.level_up, suspicious=self.policy.last_transition_suspicious,
                       last_hashed_frame=self.policy.last_hashed_frame, last_action=self.policy.last_action)
        result = original_act(self)
        try:
            audit(self.policy.graph_explorer)
        except RuntimeError as exc:
            failures.append(str(exc))
            raise
        return result

    def reset(self, obs):
        events.append({'reset': True, 'action_counter': self.policy.action_counter,
                       'previous_frame': self.policy.last_hashed_frame,
                       'previous_action': self.policy.last_action, 'level': obs.levels})
        return original_reset(self, obs)

    GraphExplorer.reset = graph_reset
    ExploreAgent.__init__ = initialize
    ExploreAgent.act = act
    ExploreAgent.after_reset = reset
    results = []
    for seed in args.seeds:
        events.clear()
        result = run('ft09', 'explore', seed, 500, 8, args.output, args.environments)
        results.append(result)
        (args.output / f'edge-events-{seed}.json').write_text(
            json.dumps(events, indent=2, default=serialize) + '\n', encoding='utf-8')
        print(json.dumps(result), flush=True)
    report = {'results': results, 'topology_audit_failures': failures,
              'source_sha256': {str(p.relative_to(arc)): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in [arc / 'explore_agent.py', arc / 'vendor/explore/graph_explorer.py']}}
    (args.output / 'diagnosis.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    return int(any(r['error'] for r in results) or bool(failures))


if __name__ == '__main__':
    raise SystemExit(main())
