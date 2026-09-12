from pathlib import Path
import os,json,subprocess,sys
root=Path(__file__).resolve().parents[1]
config=json.loads((root/'build/environment.json').read_text())
env=dict(os.environ,LEAN_PATH=config['leanPath'])
raise SystemExit(subprocess.call([config['lean'],*sys.argv[1:]],env=env,cwd=root/'Lean'))
