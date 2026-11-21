import Formalism.LocalToGlobal.CharacterGerms.RowTieCartTop

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

def PTExFBSt : Prop :=
  AllFB fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, ∀ c, x 0 (Sum.inl c) = w c

def PTAvgFBSt : Prop :=
  AllFB fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (x : ℕ → I g ⊕ JJ I g → C), x ∈ X.TySet V g →
    (∀ n, X.tyC g n ≠ a → x 0 n = 0) →
    ∃ x' ∈ X.TySet V g, x' 0 = x 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x' i n = 0


end Formalism.L2.FormalSeriesBounds
