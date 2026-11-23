module

public import Formalism.LocalToGlobal.HermitianForms.TiedSym
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentTypeLevelCharacterFiniteOrderRootsOfUniStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem formsTiedSym_chi_zero_finite : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), (∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)) → ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U, (((Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ) :=
  fun D _ _ _ Tf h =>
    GlobalTheory.T.unipotentTypeLevel_character_finiteOrder_rootsOfUnity _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Tf.glev0 D.what₂.LL D.what₂.embLL D.host.g_prime (fun i => (h i).1)

end GlobalTheory
