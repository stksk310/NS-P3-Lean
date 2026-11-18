"""Read-only bounded arithmetic and manuscript integrity checks (Python stdlib).

Default: print the deterministic report. --receipt PATH creates a new UTF-8/LF
JSON file exclusively; existing files are refused. No Lean execution occurs.
"""
import sys
sys.dont_write_bytecode = True

import argparse
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
import hashlib
import json
import math
import re
import runpy
import capacity_arithmetic as ar


def verify_source(text):
    labels = re.findall(r'\\label\{([^}]+)\}', text)
    assert len(labels) == len(set(labels)), 'Duplicate labels'
    refs = re.findall(r'\\(?:ref|eqref)\{([^}]+)\}', text)
    refs += re.findall(r'\\hyperref\[([^\]]+)\]', text)
    assert not (set(refs) - set(labels)), 'Missing reference target'
    keys = set(re.findall(r'\\bibitem\{([^}]+)\}', text))
    cited = {key.strip()
             for group in re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]+)\}', text)
             for key in group.split(',')}
    assert cited <= keys, 'Missing bibliography key'
    tags = re.findall(r'\\tag\{([^}]+)\}', text)
    assert tags, 'No numbered equation tags found'
    grouped = {}
    for tag in tags:
        match = re.fullmatch(r'(.+)\.(\d+)', tag)
        assert match, f'Unexpected equation tag format: {tag}'
        prefix, number = match.groups()
        grouped.setdefault(prefix, []).append(int(number))
    for prefix, numbers in grouped.items():
        assert numbers == list(range(1, len(numbers) + 1)), \
            f'Equation tags for {prefix} are not contiguous from 1: {numbers}'
    clean = re.sub(r'(?<!\\)%[^\n]*', '', text)
    depth = 0
    for index, character in enumerate(clean):
        if index and clean[index - 1] == '\\':
            continue
        if character == '{':
            depth += 1
        elif character == '}':
            depth -= 1
        assert depth >= 0, 'Unbalanced TeX closing brace'
    assert depth == 0, 'Unbalanced TeX braces'
    return {'labels': len(labels), 'references': len(refs),
            'bibliography_keys': len(keys), 'equation_tags': len(tags),
            'equation_tag_groups': {key: len(value) for key, value in grouped.items()}}


def report(source):
    text = source.read_text(encoding='utf-8-sig')
    integrity = verify_source(text)
    details = {}
    for name in ('verify_A3_8.py', 'verify_width_three_arithmetic.py',
                 'verify_width_one_two_arithmetic.py'):
        buffer = StringIO()
        with redirect_stdout(buffer):
            runpy.run_path(str(Path(__file__).with_name(name)), run_name='__main__')
        details[name] = json.loads(buffer.getvalue())
    assert details['verify_A3_8.py']['total_weight_pairs'] == 4154
    capacity = ar.verify_capacity(text)
    equality = []
    for m in range(4, 1001):
        C, _, _ = ar.macaulay(m)
        T = 2 + math.isqrt(4 * m)
        assert C >= T and ((C == T) == (m <= 9)), (m, C, T)
        if C == T:
            equality.append(m)
    return {
        'status': 'PASS',
        'scope': 'Bounded arithmetic and source integrity only; no Lean run or whole-theorem certification.',
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        **integrity, 'checks': details, 'capacity_tables': capacity,
        'macaulay': {'range': [4, 1000], 'values_checked': 997,
                     'equality_multiplicities': equality, 'strict_comparisons': 991},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path,
                        default=Path(__file__).resolve().parent.parent / 'manuscript/PAPER_V03.tex')
    parser.add_argument('--receipt', type=Path,
                        help='Create this new report file; refuse an existing path.')
    args = parser.parse_args()
    result = report(args.source)
    payload = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + '\n'
    if args.receipt is not None:
        try:
            with args.receipt.open('x', encoding='utf-8', newline='\n') as output:
                output.write(payload)
        except FileExistsError:
            parser.error(f'receipt already exists; refusing overwrite: {args.receipt}')
    print(payload, end='')


if __name__ == '__main__':
    main()
