"""Run ARC3 Explorer or the comparison agents through the offline evaluator."""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE/'runtime'))
sys.path.insert(0, str(HERE))

from arc3.evaluate import main

if __name__ == '__main__':
    if '--version' in sys.argv[1:]:
        print('ARC3 Explorer '+(HERE/'VERSION').read_text().strip())
        raise SystemExit(0)
    if not any(a == '--agents' or a.startswith('--agents=') for a in sys.argv[1:]):
        sys.argv.extend(['--agents', 'explore'])
    main()
