import pyaml
import yaml
from pathlib import Path
import sys

try:
    Path(sys.argv[2]).write_text(pyaml.dump(yaml.safe_load(open(sys.argv[1]))))
except yaml.reader.ReaderError as err:
    print(f"Error while reading input yaml file: {err}")
    exit(1)
