import Mathlib

namespace KStar.Choice

structure IsLevelPair (N a b : ℕ) : Prop where
  prime_fst : a.Prime
  prime_snd : b.Prime
  ne_two : a ≠ 2
  lt : a < b
  lt_two_mul : b < 2 * a
  not_dvd_fst : ¬ a ∣ N
  not_dvd_snd : ¬ b ∣ N

example : IsLevelPair 1 3 5 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

noncomputable def levelFst (N : ℕ) : ℕ := sInf {a | ∃ b, IsLevelPair N a b}

noncomputable def levelSnd (N : ℕ) : ℕ := sInf {b | ∃ a, IsLevelPair N a b}

noncomputable def levelSnd' (N : ℕ) : ℕ := sInf {b | IsLevelPair N (levelFst N) b}



end KStar.Choice
