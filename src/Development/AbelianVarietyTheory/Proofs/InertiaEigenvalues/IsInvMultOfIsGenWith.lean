module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DiagonalQuotientEigen

@[expose] public section

noncomputable section

namespace GlobalTheory.SenCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

section Operators

variable {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
  [IsScalarTower O A D]

variable {π : A} {g : D →ₗ[O] D} {P Q : Submodule O D}

end Operators

section Residue

variable {O : Type} [CommRing O]

end Residue

section Sen

variable {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
  [IsScalarTower O A D] [IsDomain O] [IsDiscreteValuationRing O]

end Sen

section Wach

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

section RankOne

variable {r : ℕ} (hr : r = 1) (β : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (hβ : ∀ k, (β k : W.DD T) ∈ W.NΔ T)
include hr hβ

end RankOne

end Wach

section Prime

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P)

variable {K LL : FinExt l} (hA : CaseA K LL)

theorem standing_iff {hg : Good K 1 LL} (lam : ↥(OL LL)) :
    Standing P K LL (H.W K 1 LL hg).emb lam ↔ 5 ≤ l ∧ CaseA K LL ∧ Irreducible lam :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.2.2.2⟩, fun h => ⟨h.1, h.2.1, by rw [show K0 K = K.1 from inf_eq_left.2 h.2.1.1],
    (H.W K 1 LL hg).emb_bij, (H.W K 1 LL hg).emb_σ, h.2.2⟩⟩

end Prime

end GlobalTheory.SenCompare
