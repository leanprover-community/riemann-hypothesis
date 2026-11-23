module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajorD
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajorC
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7} {a b : ℕ}

theorem row_smul (i : Fin a) (c : AE D) (x : Mx D a b) : row i (c • x) = c • row i x := by
  rfl

theorem intOff_row {S : Finset (Pl D)} {x : Mx D a b} (hx : IntOff S x) (i : Fin a) : IntOff S (row i (sF D • x)) := by
  intro v hv i' j
  show cv D v (sF D * x i j) ∈ _
  rw [cv_sF]
  exact hx v hv i j

theorem not_intOff_row {S : Finset (Pl D)} {x : Mx D a b} (hx : ¬ IntOff S x) :
    ∃ i, ¬ IntOff S (row i (sF D • x)) := by
  by_contra hcon
  push Not at hcon
  apply hx
  intro v hv i j
  have e := hcon i v hv 0 j
  have e' : cv D v (sF D * x i j) ∈ GlobalTheory.AdelicU.intLoc (↥D.host.F) D.host.E v := e
  rwa [cv_sF] at e'




theorem bumpMaj (hB : BumpEx) (θ : InfFam D) (hθ : IsInfFam θ) {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e)
    (K : Set (Mx D a b)) (hK : IsCompact K) (F₀ : SchwartzMap (D.what₂.Tau → Fin a → Fin b → ℂ) ℂ)
    (hF₀ : ∀ y, 0 ≤ (F₀ y).re ∧ (F₀ y).im = 0) :
    ∃ Φ₀ ∈ schwartzA θ a b, Good S e Φ₀ ∧ (∀ x, 0 ≤ (Φ₀ x).re ∧ (Φ₀ x).im = 0) ∧
      ∀ x, IntOff S x → GlobalTheory.Unf.InBox K x → Φ₀ x = F₀ (cA θ x) := by
  have hCint : ∀ y ∈ (fun k => sF D • (e • k)) '' K, IntOff S y := by
    rintro _ ⟨k, -, rfl⟩ v hv i j
    show cv D v (sF D * (e * k i j)) ∈ _
    rw [cv_sF, map_mul, he.2 v, if_neg hv, zero_mul]
    exact (GlobalTheory.AdelicU.intLoc _ _ v).zero_mem
  obtain ⟨η, hη⟩ := hB D θ hθ a b S e he _
    (hK.image ((continuous_const_smul (sF D)).comp (continuous_const_smul e))) hCint
  have hG : ∀ i, ∃ G ∈ GlobalTheory.WeilM.SB (Fin 1 → Fin b → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af ↥D.host.F) D.host.E),
      ∀ y : Mx D 1 b, η i (sF D • y) = G fun i' j => finPart D (y i' j) :=
    fun i => rowSB θ (sF D) infPart_sF finPart_sF (η i) (hη i).1
  choose G hGSB hGeq using hG
  set Ψ : Mx D a b → ℂ := fun x => ∏ i, η i (sF D • row i x) with hΨ
  have hΨG : ∀ x, Ψ x = (fun z => ∏ i, G i fun _ j => z i j) (fun i j => finPart D (x i j)) := by
    intro x
    exact Finset.prod_congr rfl fun i _ => hGeq i (row i x)
  have hΨgood : Good S e Ψ := by
    intro x
    by_cases hx : IntOff S x
    · rw [if_pos hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← row_smul, (hη i).2.2.1, if_pos (intOff_row hx i), ← row_smul, ← row_smul, smul_comm e (sF D) x]
    · rw [if_neg hx]
      obtain ⟨i, hi⟩ := not_intOff_row hx
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [← row_smul, (hη i).2.2.1, if_neg hi]
  refine ⟨fun x => F₀ (cA θ x) * Ψ x, ?_, good_mul θ he hΨgood (fun z => F₀ z), ?_, ?_⟩
  · apply Submodule.subset_span
    refine ⟨F₀, fun z => ∏ i, G i fun _ j => z i j, prodSB G hGSB, ?_⟩
    funext x
    rw [hΨG x]
  · intro x
    exact re_im_mul (hF₀ _) (re_im_prod _ _ fun i => ⟨((hη i).2.2.2.1 _).1, ((hη i).2.2.2.1 _).2.2⟩)
  · rintro x hx ⟨k, hk, hxk⟩
    have hfin : ∀ i j, finPart D (x i j) = finPart D (k i j) := by
      intro i j
      have h0 := congrFun (congrFun hxk i) j
      simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.zero_apply] at h0
      exact sub_eq_zero.mp h0
    suffices h1 : Ψ x = 1 by
      show F₀ (cA θ x) * Ψ x = F₀ (cA θ x)
      rw [h1, mul_one]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← row_smul, (hη i).2.2.1, if_pos (intOff_row hx i), ← row_smul, smul_comm e (sF D) x, row_smul, hGeq i]
    have hfun : (fun i' j => finPart D ((row i (e • x)) i' j)) = (fun i' j => finPart D ((row i (e • k)) i' j)) := by
      funext i' j
      show finPart D (e * x i j) = finPart D (e * k i j)
      rw [map_mul, map_mul, hfin]
    rw [hfun, ← hGeq i, ← row_smul]
    exact (hη i).2.2.2.2 _ ⟨k, hk, rfl⟩

end PositivityTheory.Rg.Rsw.L.LMajor

end
