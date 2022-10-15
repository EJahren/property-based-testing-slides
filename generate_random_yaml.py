import hypothesis.strategies as st
from pathlib import Path
import sys
import warnings

with warnings.catch_warnings():
    warnings.simplefilter("ignore")
    Path(sys.argv[1]).write_text(st.text().example())
