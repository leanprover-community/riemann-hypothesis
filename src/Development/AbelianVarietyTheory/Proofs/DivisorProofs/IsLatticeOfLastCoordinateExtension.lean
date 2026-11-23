module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem latLast_isLattice : ∀ {E : Type} [Field E] [NumberField E] {n N : ℕ} (hN : N = n + 1)
    (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    Submodule.IsLattice E L := by
  intro E _ _ n N hN M L hM hL
  subst hN
  have hiC : ∀ k : Fin n, Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) k = Fin.castSucc k := fun k => Fin.ext rfl
  have hiL : Formalism.L2.Col.Br.iL (rfl : n + 1 = n + 1) = Fin.last n := Fin.ext rfl
  simp only [hiC, hiL] at hL
  let g : (Fin n → E) →ₗ[E] (Fin (n + 1) → E) :=
    { toFun := fun x => Fin.snoc (α := fun _ => E) x 0
      map_add' := by
        intro x y; ext j
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
      map_smul' := by
        intro a x; ext j
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp }
  have gC : ∀ x k, g x (Fin.castSucc k) = x k := fun x k => by simp [g]
  have gL : ∀ x, g x (Fin.last n) = 0 := fun x => by simp [g]
  let e : Fin (n + 1) → E := Pi.single (Fin.last n) 1
  have gm : ∀ m ∈ M, g m ∈ L := fun m hm => (hL _).2 ⟨by simpa [gC] using hm, 0, by simp [gL]⟩
  have he : e ∈ L := (hL _).2 ⟨by
      have : (fun k : Fin n => e (Fin.castSucc k)) = 0 := by
        funext k; simp [e, Pi.single_apply, Fin.castSucc_ne_last]
      rw [this]; exact M.zero_mem, 1, by simp [e]⟩
  have dec : ∀ x : Fin (n + 1) → E, x = g (fun k => x (Fin.castSucc k)) + x (Fin.last n) • e := by
    intro x; ext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [gL, e]
    · simp [gC, e, Pi.single_apply, Fin.castSucc_ne_last]
  have hLeq : L = M.map (g.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {e} := by
    apply le_antisymm
    · intro v hv
      obtain ⟨hvM, c, hc⟩ := (hL v).1 hv
      rw [dec v]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_map_of_mem hvM))
        (Submodule.mem_sup_right ?_)
      have hs : (c : E) • e = c • e := algebraMap_smul E c e
      rw [← hc, hs]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self e)
    · exact sup_le (Submodule.map_le_iff_le_comap.2 fun m hm => gm m hm)
        (Submodule.span_le.2 (by simpa using he))
  refine ⟨?_, ?_⟩
  · rw [hLeq]
    exact Submodule.FG.sup (hM.fg.map _) (Submodule.fg_span_singleton e)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory
