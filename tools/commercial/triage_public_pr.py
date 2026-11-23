#!/usr/bin/env python3
"""Read-only, public-GitHub PR intake for a bounded Lean CI audit.

The output is qualification evidence, not proof that CI covers a claim.
Uses GitHub's REST API, never clones/runs third-party code.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
import re
import sys
import urllib.error
import urllib.request

PR_URL = re.compile(r"\Ahttps://github\.com/([A-Za-z0-9][A-Za-z0-9_.-]{0,99})/([A-Za-z0-9_.-]{1,100})/pull/(\d{1,9})/?\Z")
SHA = re.compile(r"\A[0-9a-f]{40}\Z")
MAX_PAGES = 30  # GitHub caps PR-files listing at 3000 files


def parse_pr_url(url):
    match = PR_URL.fullmatch(url)
    if not match or '..' in match.group(1) or '..' in match.group(2) or match.group(2).endswith('.git'):
        raise ValueError("only canonical https://github.com/OWNER/REPO/pull/N URLs are accepted")
    owner, repo, number = match.groups()
    if not int(number):
        raise ValueError("PR number must be positive")
    return owner, repo, int(number)


def fetch_json(path, token=None):
    # All endpoints are constructed internally; never fetch URLs found in API responses.
    url = 'https://api.github.com' + path
    req = urllib.request.Request(url, headers={
        'Accept': 'application/vnd.github+json',
        'User-Agent': 'primitive-lean-public-pr-intake/1.0',
        'X-GitHub-Api-Version': '2022-11-28',
        **({'Authorization': 'Bearer ' + token} if token else {})
    })
    try:
        with urllib.request.urlopen(req, timeout=15) as response:
            if response.geturl().split('/')[2].lower() != 'api.github.com':
                raise ValueError('GitHub API unexpectedly redirected to another host')
            return json.load(response)
    except urllib.error.HTTPError as e:
        if e.code == 403:
            raise RuntimeError('GitHub API denied request or rate limit exceeded (403)') from None
        if e.code == 404:
            raise RuntimeError('public PR/API endpoint not found (404)') from None
        raise RuntimeError(f'GitHub API HTTP {e.code}') from None


def is_audit_file(path):
    return path.endswith(('.lean', '.inc')) or path.startswith('.github/workflows/')


def triage(url, get=fetch_json, token=None, max_audit_files=10):
    owner, repo, number = parse_pr_url(url)
    base_path = f'/repos/{owner}/{repo}'
    pr = get(f'{base_path}/pulls/{number}', token)
    head_sha = pr.get('head', {}).get('sha')
    if not isinstance(head_sha, str) or not SHA.fullmatch(head_sha):
        raise ValueError('PR API omitted a valid head SHA')
    changed_total = pr.get('changed_files')
    if not isinstance(changed_total, int) or changed_total < 0:
        raise ValueError('PR API omitted changed_files count')
    file_rows = []
    if changed_total <= 3000:
        for page in range(1, MAX_PAGES + 1):
            rows = get(f'{base_path}/pulls/{number}/files?per_page=100&page={page}', token)
            if not isinstance(rows, list):
                raise ValueError('Unexpected files API response')
            file_rows.extend(rows)
            if len(rows) < 100:
                break
    # If files response is incomplete, never claim eligible.
    inventory_complete = changed_total <= 3000 and len(file_rows) == changed_total
    audit_files = sorted({f['filename'] for f in file_rows if isinstance(f.get('filename'), str) and is_audit_file(f['filename'])})
    # This endpoint is a bounded snapshot, not exhaustive check-run evidence.
    runs = get(f'{base_path}/actions/runs?head_sha={head_sha}&per_page=100', token)
    if not isinstance(runs, dict) or not isinstance(runs.get('workflow_runs'), list):
        raise ValueError('Unexpected Actions runs API response')
    matched_runs = []
    for run in runs['workflow_runs']:
        if run.get('head_sha') != head_sha:
            continue
        matched_runs.append({key: run.get(key) for key in ('id', 'name', 'event', 'status', 'conclusion', 'html_url', 'created_at')})
    matched_runs.sort(key=lambda r: (str(r['id']), str(r['created_at'])))
    in_scope = inventory_complete and 0 < len(audit_files) <= max_audit_files
    issues = []
    if not inventory_complete:
        issues.append('file_inventory_incomplete')
    if not audit_files:
        issues.append('no_lean_or_workflow_files_detected')
    if len(audit_files) > max_audit_files:
        issues.append('changed_lean_or_workflow_files_exceed_limit')
    if not matched_runs:
        issues.append('no_matching_actions_runs_in_first_page')
    return {
        'schema_version': 1,
        'kind': 'public_pr_audit_intake',
        'retrieved_at_utc': datetime.now(timezone.utc).isoformat(timespec='seconds'),
        'source': {'pr_url': f'https://github.com/{owner}/{repo}/pull/{number}', 'head_sha': head_sha,
                   'base_sha': pr.get('base', {}).get('sha'), 'state': pr.get('state'),
                   'draft': pr.get('draft'), 'changed_files_reported': changed_total},
        'intake': {'eligible_for_manual_scope_review': in_scope, 'maximum_audit_files': max_audit_files,
                   'audit_file_count': len(audit_files), 'audit_files': audit_files,
                   'all_changed_files_observed': len(file_rows), 'inventory_complete': inventory_complete,
                   'issues': issues},
        'observed_actions_runs': matched_runs,
        'evidence_limitations': [
            'This is a static API snapshot. Runs for synthetic merge SHAs or other CI providers may be missing.',
            'Only the first 100 Actions workflow runs with the exact PR head SHA are examined.',
            'A successful run does not prove the changed declarations or requested claim were checked.',
            'No workflow logs, artifacts, Lean elaboration, kernel proof or axiom audit is performed.',
            'Eligibility is only for manual review; no acceptance, price, delivery date, or payment is implied.'
        ],
        'api_evidence_urls': [
            f'https://api.github.com{base_path}/pulls/{number}',
            f'https://api.github.com{base_path}/pulls/{number}/files?per_page=100&page=1',
            f'https://api.github.com{base_path}/actions/runs?head_sha={head_sha}&per_page=100'
        ]
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('public_pr_url')
    parser.add_argument('--output', help='JSON output path; default stdout')
    args = parser.parse_args(argv)
    try:
        report = triage(args.public_pr_url, token=os.environ.get('GH_TOKEN'))
        output = json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + '\n'
        if args.output:
            with open(args.output, 'w', encoding='utf-8') as stream:
                stream.write(output)
        else:
            sys.stdout.write(output)
    except (ValueError, RuntimeError, OSError) as e:
        print(f'intake failed: {e}', file=sys.stderr)
        return 2
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
