module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusIdempotentImageSiegel
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.exists_open_locus_idempotent_image_siegel : ∀ (h h' M d : ℕ) (O : Type) [Ring O] (bar : O → O) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → e * e = e → ∃ (U : S'.Opens) (c : SiegPre h M (zetaAway M) (U.ι ≫ t)) (w : SiegPre h' M (zetaAway M) (U.ι ≫ t)) (actw : O → (w.A ⟶ w.A)), SiegKerBy c d ∧ IsUnit ((d : ℕ) : Γ(U.toScheme, ⊤)) ∧ w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act U.ι ∧ ZRel e jl o κ c w actw ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)), IsUnit ((d : ℕ) : Γ(T, ⊤)) → SiegKerBy c' d → (∃ (w' : SiegPre h' M (zetaAway M) (g ≫ t)) (actw' : O → (w'.A ⟶ w'.A)), ActPB w' actw' z act g ∧ ZRel e jl o κ c' w' actw') → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.IdemLocus.exists_open_locus) | (exact GlobalTheory.IdemLocus.exists_open_locus) | (intros; apply GlobalTheory.IdemLocus.exists_open_locus  <;> assumption)
