"""Compare paired public diagnostics, including stopped trials in the means."""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import statistics


def index(root):
    rows = json.loads((root / 'summary.json').read_text(encoding='utf-8'))
    mapped = {(r['game'], r['agent'], r['seed']): r for r in rows}
    if len(mapped) != len(rows):
        raise ValueError('Duplicate trial identity')
    return mapped


def aggregate(rows):
    return dict(trials=len(rows), errors=sum(r['error'] is not None for r in rows),
                error_types=dict(Counter(r['error'] for r in rows if r['error'])),
                wins=sum(r['win'] for r in rows),
                levels_mean=statistics.mean(r['best_levels_completed'] for r in rows),
                levels_total=sum(r['best_levels_completed'] for r in rows),
                calls_total=sum(r['calls_including_initial_reset'] for r in rows),
                gameplay_actions_total=sum(r['gameplay_actions'] for r in rows),
                resets_total=sum(r['resets_after_initial'] for r in rows),
                seconds_total=round(sum(r['seconds'] for r in rows), 3),
                seconds_mean=round(statistics.mean(r['seconds'] for r in rows), 3),
                recoveries=dict(sum((Counter(r.get('policy_recoveries', {})) for r in rows), Counter())))


def trace_hash(path):
    # Windows and Linux text writers differ in newline bytes only.
    return hashlib.sha256(gzip.open(path, 'rb').read().replace(b'\r\n', b'\n')).hexdigest()


def trace_path(root, game, agent, seed):
    # The evaluator accepts both catalog IDs and short prefixes.
    for identity in (game, game.split('-', 1)[0]):
        path = root / f'{identity}-{agent}-{seed}.jsonl.gz'
        if path.is_file():
            return path
    raise FileNotFoundError(f'Missing trace: {game}/{agent}/{seed}')


def compare(before, after):
    a, b = index(before), index(after)
    if a.keys() != b.keys():
        raise ValueError('Trial sets differ')
    report = {'scope': 'Public Demo diagnostics; not hidden-environment generalization or an official score',
              'timing_scope': 'Per-trial evaluator wall time; includes initialization, excludes tests and downloading',
              'before_total': aggregate(list(a.values())), 'after_total': aggregate(list(b.values())),
              'groups': [], 'trials': []}
    for game, agent in sorted({k[:2] for k in a}):
        keys = sorted(k for k in a if k[:2] == (game, agent))
        report['groups'].append({'game': game, 'agent': agent,
                                 'before': aggregate([a[k] for k in keys]),
                                 'after': aggregate([b[k] for k in keys])})
    for key in sorted(a):
        game, agent, seed = key
        fields = ['error', 'best_levels_completed', 'calls_including_initial_reset',
                  'gameplay_actions', 'resets_after_initial', 'seconds', 'final_status']
        report['trials'].append({'game': game, 'agent': agent, 'seed': seed,
                                 'before': {k: a[key][k] for k in fields},
                                 'after': {k: b[key][k] for k in fields},
                                 'trace_equal': trace_hash(trace_path(before, *key)) == trace_hash(trace_path(after, *key))})
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--before', type=Path, required=True)
    parser.add_argument('--after', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = compare(args.before, args.after)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: report[k] for k in ('before_total', 'after_total', 'groups')}, indent=2))


if __name__ == '__main__':
    main()
