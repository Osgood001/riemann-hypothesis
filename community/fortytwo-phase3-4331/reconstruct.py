"""Reconstruct the exact proof from its organizer shard. Requires Python 3.14 and git."""
import argparse
import hashlib
import json
import os
import re
import subprocess
import tarfile
import tempfile
from pathlib import Path, PurePosixPath

def digest(data):
    return hashlib.sha256(data).hexdigest()

def inventory_digest(files):
    result = hashlib.sha256()
    for key in sorted(files):
        result.update(key.encode('utf-8') + b'\0' + hashlib.sha256(files[key]).digest())
    return result.hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('core', choices=['14', '23', '24', '25'])
    parser.add_argument('shard', type=Path)
    parser.add_argument('output', type=Path, help='new directory for the reconstructed Lean sources')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent / ('core' + args.core)
    record = json.loads((here / 'verification.json').read_text())
    with args.shard.open('rb') as source:
        if hashlib.file_digest(source, 'sha256').hexdigest() != record['shard_sha256']:
            raise SystemExit('Source archive differs from the organizer release.')
    if args.output.exists():
        raise SystemExit('Choose a new output directory.')
    contents = {}
    with tarfile.open(args.shard, 'r|zst') as archive:
        for member in archive:
            name = PurePosixPath(member.name)
            if name.is_absolute() or '..' in name.parts:
                raise ValueError('Unexpected archive path')
            if name.parts[:1] != ('src',) or name.suffix != '.lean':
                continue
            key = name.relative_to('src').as_posix()
            if not member.isfile() or key in contents:
                raise ValueError('Unexpected source entry: ' + key)
            contents[key] = archive.extractfile(member).read()
    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp)
        for key, checks in record['modified_files'].items():
            if digest(contents[key]) != checks['before']:
                raise ValueError('Baseline source differs: ' + key)
            path = base / key
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(contents[key])
        env = {key:value for key,value in os.environ.items() if not key.startswith('GIT_')}
        env['GIT_CEILING_DIRECTORIES'] = str(base.parent)
        subprocess.run(['git', '-c', 'core.autocrlf=false', 'apply', '--whitespace=nowarn', str(here / 'changes.patch')], cwd=base, env=env, check=True)
        for key, checks in record['modified_files'].items():
            data = (base / key).read_bytes()
            if digest(data) != checks['after']:
                raise ValueError('Patched source differs: ' + key)
            contents[key] = data
    solution = (here / 'Solution.lean').read_bytes()
    result = {'Solution.lean': solution}
    pending = [solution]
    while pending:
        body = pending.pop()
        for module in re.findall(r'^import\s+(\S+)', body.decode('utf-8'), re.MULTILINE):
            key = module.replace('.', '/') + '.lean'
            if key in contents and key not in result:
                result[key] = contents[key]
                pending.append(contents[key])
    if len(result) != record['submitted_files'] or inventory_digest(result) != record['proof_tree_sha256']:
        raise SystemExit('The reconstructed sources differ from the locally kernel-verified proof.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=args.output.parent) as tmp:
        stage = Path(tmp) / 'proof'
        stage.mkdir()
        for key, body in result.items():
            dest = stage / key
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(body)
        stage.rename(args.output)
    print(f"Core {args.core}: {len(result)} proof files, SHA-256 {record['proof_tree_sha256']}")

if __name__ == '__main__':
    main()
