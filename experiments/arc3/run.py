"""Run all three agents through the shared offline ARC evaluator."""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE/'runtime'))
sys.path.insert(0, str(HERE))

from arc3.evaluate import main

if __name__ == '__main__':
    main()
