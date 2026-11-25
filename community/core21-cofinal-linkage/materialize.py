"""Usage: python3 materialize.py EXTRACTED_CORE21_SHARD OUTPUT_PROOF

Use the published Core 21 shard, extracted after verifying the release SHA-256.
Place solution.patch next to this script.
"""
import argparse
import hashlib
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory


IMPORT = re.compile(rb"^import ([^\s]+)", re.MULTILINE)
FILE_COUNT = 38_995
BASE = ("Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/"
        "ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean")
BASE_SHA256 = "e761e876e3236895eec1b67b5a2118846ddfcc6883eed367ac6cc78523da15f2"
PATCH_SHA256 = "72790e46b3a98aff66ab580316a8747d793c6ec8e43f8784c9411ee7e35d3880"
SOLUTION_SHA256 = "076f164f2aeede3389d36d3c0d01698e7fca1c4de49f603a44939ce1e2c044cf"
TREE_SHA256 = "cf5e619d8a1acf9671fa421adf013c31f19d1c2e8fce8a379e983371b6c4c2a4"


def check(data: bytes, expected: str, name: str) -> None:
    if hashlib.sha256(data).hexdigest() != expected:
        raise ValueError(f"Unexpected {name} checksum")


def materialize(shard: Path, output: Path) -> None:
    if output.exists():
        raise FileExistsError(f"Output must not already exist: {output}")
    shard_sources = shard / "src"
    available = {path.relative_to(shard_sources).as_posix(): path
                 for path in shard_sources.rglob("*.lean")}
    if len(available) != 61_171:
        raise ValueError("Expected 61,171 source files in the Core 21 shard")
    base = available[BASE]
    check(base.read_bytes(), BASE_SHA256, "original entry")
    patch = Path(__file__).with_name("solution.patch").read_bytes()
    check(patch, PATCH_SHA256, "patch")

    pending = ["Solution.lean"]
    visited = {}
    output.parent.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(dir=output.parent) as temp:
        solution = Path(temp) / "Solution.lean"
        subprocess.run(["patch", "-s", "-o", str(solution), str(base)],
                       input=patch, check=True)
        check(solution.read_bytes(), SOLUTION_SHA256, "patched Solution.lean")
        available["Solution.lean"] = solution

        proof = Path(temp) / "proof"
        proof.mkdir()
        while pending:
            name = pending.pop()
            if name in visited:
                continue
            data = available[name].read_bytes()
            visited[name] = hashlib.sha256(data).hexdigest()
            pending.extend(
                dep for module in IMPORT.findall(data)
                if (dep := module.decode().replace(".", "/") + ".lean") in available
            )
            dest = proof / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)

        tree_digest = hashlib.sha256()
        for name, digest in sorted(visited.items()):
            tree_digest.update(f"{name} {digest}\n".encode())
        print(f"{len(visited):,} Lean files; SHA-256 {tree_digest.hexdigest()}")
        if len(visited) != FILE_COUNT or tree_digest.hexdigest() != TREE_SHA256:
            raise ValueError("Unexpected Core 21 proof tree")
        proof.rename(output)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("shard", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    materialize(args.shard, args.output)
