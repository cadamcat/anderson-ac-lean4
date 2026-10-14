import Lake
open Lake DSL

package AndersonAC where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- OpenAI's mathematics library (Apache-2.0), directory `lean` of openai/math.
require OAI from git
  "https://github.com/openai/math.git" @ "adc7f1241b42e322a6451854ab7e4b4c146bf78a" / "lean"

@[default_target]
lean_lib AndersonAC
