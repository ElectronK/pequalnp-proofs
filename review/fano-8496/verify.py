"""Replay the L-meta-8496 reduction and its proved first obligation."""

import os
from pathlib import Path
import subprocess


def main():
    sources = Path(__file__).resolve().parent
    project = sources.parents[1] / "lean"
    objects = project / ".lake" / "build" / "fano-8496-review"
    objects.mkdir(parents=True, exist_ok=True)

    reduction = "PEqualNP.Outside.R_meta_8496_1"
    subprocess.run(
        ["lake", "build", "PEqualNP.Outside.L_meta_17415", "PEqualNP.Outside.L_meta_4647", reduction],
        cwd=project,
        check=True,
    )
    subprocess.run(
        ["lake", "env", "lean", "--run", "CheckLemma.lean", reduction, str(sources / "statement.txt"), "reduce"],
        cwd=project,
        check=True,
    )

    modules = (
        "FanoOrdinary", "MultipleSharing", "P8Structure", "NestedFanoIrredundancy",
        "NestedFanoPositive", "FanoRestriction", "NestedFanoDepth", "NestedFanoTree",
        "NestedFanoLive", "NestedFanoMass", "NestedFanoDirty", "NestedFanoPaths",
        "NestedFanoGeometry", "NestedFanoCutChild", "VerifiedFanoCutHandoff", "NestedFanoWitness28",
    )
    env = os.environ.copy()
    paths = [str(objects)]
    if env.get("LEAN_PATH"):
        paths.append(env["LEAN_PATH"])
    env["LEAN_PATH"] = os.pathsep.join(paths)
    for module in modules:
        print(f"Checking {module}", flush=True)
        subprocess.run(
            ["lake", "env", "lean", f"--root={sources}", "-o", str(objects / f"{module}.olean"),
             str(sources / f"{module}.lean")],
            cwd=project,
            env=env,
            check=True,
        )


if __name__ == "__main__":
    main()
