module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackCartierDivisorBundleEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberZeroSmallImage
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush

theorem Dbl.num_eq_zero_of_isPull : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ (q : W.Z ⟶ Y.X) [IsDominant q] (y : Fin (Y.dim + 1) → CartierDiv W.Z) (e : Fin (Y.dim + 1) → Y.Dv), (∀ i, IsPull q (y i) (e i)) → W.num y = 0 := by
  intro F _ Y W hW q _ y e h
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hp : IsProjOver (strHom F (X := W.Z)) := by
    rw [strHom_eq (f := W.p₁ ≫ Y.str) fun _ => rfl]
    exact W.proj
  have hd : topologicalKrullDim W.Z ≤ (0 + (Y.dim + 1) : ℕ) := by
    rw [Nat.zero_add]; exact hW
  have hg : topologicalKrullDim (closure ({q (genericPoint W.Z)} : Set Y.X)) < (Y.dim + 1 : ℕ) := by
    refine lt_of_le_of_lt (topologicalKrullDim_subspace_le _ _) ?_
    rw [Y.topologicalKrullDim_eq]
    exact_mod_cast Nat.lt_succ_self _
  have key := GlobalTheory.PullVanish.interNum_pull_eq_zero F 0 (Y.dim + 1) W.Z Y.X hp hd q hg Fin.elim0
    (fun i => i.elim0) (fun i => toLB (e i)) (fun i => isLB_toLB _)
  have hL : ∀ x, (Sum.elim (Fin.elim0 : Fin 0 → LB W.Z) (fun a => (toLB (e a)).pull q) x).IsLB := by
    rintro (i | a)
    · exact i.elim0
    · exact pull_isLB (isLB_toLB _) q
  rw [← interNum_comp_equiv F _ hL (Equiv.emptySum (Fin 0) (Fin (Y.dim + 1))).symm] at key
  refine Eq.trans ?_ key
  refine interNum_congr_cls F _ (fun i => isLB_toLB _) (fun i => hL _) fun i => ?_
  exact ((cls_pull (isLB_toLB (e i)) q (pull_isLB (isLB_toLB _) q)).trans
    (GlobalTheory.Cartier.PullPres.pull_cls_toLB _ _ q (y i) (e i) (h i))).symm

end GlobalTheory.FlagPush
