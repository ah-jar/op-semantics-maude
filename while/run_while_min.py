from pathlib import Path
import subprocess

program = Path("program.while").read_text().strip().removesuffix(".")

commands = f"""
load main.maude
rew in NS-WHILE-SEMANTICS : {program} .
quit
"""

result = subprocess.run(
    ["maude"],
    input=commands,
    text=True,
    capture_output=True
)

for line in result.stdout.splitlines():
    if line.startswith("result State:"):
        print("Final State -> " + line.removeprefix("result State:").strip())
