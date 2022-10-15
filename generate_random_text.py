import hypothesis.strategies as st
import warnings

with warnings.catch_warnings():
    warnings.simplefilter("ignore")
    print(st.text().example())
