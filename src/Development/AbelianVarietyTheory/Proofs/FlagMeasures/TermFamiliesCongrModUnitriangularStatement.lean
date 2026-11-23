module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermFamiliesCongrModUnitriangular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.term_families_congr_mod_unitriangular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) {r : ℕ} (P : LocNG.FPair H r) (d : LocNG.Datum P) (τ : Loc.Term V M r) (sg : Loc.SplitG M.L), M.split = some sg → LocNG.IsTermOver P d τ → ∀ (y x : Fin (r + 1) → V) (B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → B a b = 0) → (∀ a b, b < a → B' a b = 0) → (∀ a, B' a a = B a a) → (∀ a, B a a ∈ M.L.O ∧ ∃ t ∈ M.L.O, t * B a a = 1) → (∀ b, y b = ∑ a, B a b • P.A.f a) → (∀ b, x b = ∑ a, B' a b • P.B.f a) → (∀ a, y a ∈ τ.abelian₂) → (∀ b, x b ∈ τ.abelian₂) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, ξ a b ∈ M.L.O) ∧ (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, x b - ∑ a, ξ a b • y a ∈ H.smulLat (algebraMap F E (sg.q : F)) τ.abelian₂ := by
  first | exact @GlobalTheory.loc_cong_unitri | exact GlobalTheory.loc_cong_unitri | (intros; apply GlobalTheory.loc_cong_unitri <;> assumption)
