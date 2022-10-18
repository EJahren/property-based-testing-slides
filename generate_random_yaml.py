import hypothesis.strategies as st
import warnings
import yaml

good_text = st.text(alphabet=st.characters(min_codepoint=1, blacklist_characters=["'", '"']))
with warnings.catch_warnings():
    warnings.simplefilter("ignore")
    print(yaml.dump(st.dictionaries(good_text, good_text).example()))
