#!/usr/bin/env python3
"""Check handoff structure; this does not authenticate or rerun the evidence."""
import json
from pathlib import Path
import re
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def validate(doc):
    require(isinstance(doc, dict), 'record must be an object')
    require(doc.get('schema_version') == '1.0', 'unsupported schema version')
    require(doc.get('repository') == 'Sumuji-zkdwn/primitive-lean', 'unexpected repository')
    require(bool(doc.get('id')) and bool(doc.get('recorded_at')), 'id and recorded_at are required')
    subject = doc.get('subject', {})
    sha = subject.get('head_sha', '')
    require(re.fullmatch(r'[0-9a-f]{40}', sha) is not None, 'subject head_sha must be a full commit SHA')
    require(isinstance(subject.get('pull_request'), int) and subject['pull_request'] > 0, 'PR number is required')
    require(subject.get('url', '').startswith('https://github.com/Sumuji-zkdwn/primitive-lean/pull/'), 'subject PR URL is required')
    producer = doc.get('producer', {})
    require(all(producer.get(k) for k in ('role', 'status', 'evidence', 'note')), 'producer attribution is incomplete')
    observations = doc.get('observations')
    require(isinstance(observations, list) and observations, 'observations required')
    allowed = {
        'source_observation': {'confirmed', 'unverified'},
        'independent_probe': {'pass', 'counterexample', 'fail', 'unverified'},
        'github_actions': {'success', 'failure', 'action_required', 'in_progress', 'unverified'},
        'lean_kernel': {'success', 'failure', 'unverified'},
        'hypothesis': {'unverified'},
    }
    for i, row in enumerate(observations):
        require(isinstance(row, dict), f'observation {i} must be an object')
        kind = row.get('kind')
        require(kind in allowed and row.get('status') in allowed[kind], f'observation {i} has incompatible kind/status')
        require(row.get('subject_sha') == sha, f'observation {i} describes a different head')
        require(bool(row.get('summary')) and bool(row.get('evidence')), f'observation {i} requires summary and evidence')
        if kind in {'github_actions', 'lean_kernel', 'independent_probe'}:
            require(bool(row.get('scope')), f'observation {i} requires explicit scope')
        if kind == 'github_actions':
            require(row['evidence'].startswith('https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/'), f'observation {i} requires a run URL')
    require(bool(doc.get('mathematical_claim')), 'state the mathematical claim or explicitly state none')
    require(isinstance(doc.get('unverified'), list) and len(doc['unverified']) > 0, 'unverified list required')
    action = doc.get('next_action', {})
    require(all(action.get(k) for k in ('assignee', 'task', 'completion_condition', 'status')), 'next action incomplete')
    require(action['status'] in {'not_started', 'in_progress', 'blocked', 'completed'}, 'unknown action status')


def main():
    paths = sys.argv[1:] or [str(p) for p in sorted((Path(__file__).parent / 'handoffs').glob('*.json'))]
    require(paths, 'no handoff records found')
    for path in paths:
        with open(path, encoding='utf-8') as f:
            validate(json.load(f))
        print(f'PASS structure: {path} (evidence content and truth not checked)')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, TypeError, KeyError) as exc:
        print(f'FAIL: {exc}', file=sys.stderr)
        sys.exit(1)
