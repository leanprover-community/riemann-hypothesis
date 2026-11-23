module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationLiftDeterminesModFil
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTSkew



theorem skew_of_isFilLift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (φ : LinearMap.BilinForm k (HdR o₀.A)), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, ∀ y ∈ Fil o₀.A, ∀ x' y' : HdR o₀.A, IsFilLift m'.cart x x' → IsFilLift m'.cart y y' → φ x' y + φ x y' = 0 := by
  intro p _ D R _ b N k _ t o₀ φ hφ o' m' x _ y _ x₁ y₁ hx hy
  have HR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have HD : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  obtain ⟨g', hg'⟩ := GlobalTheory.KSGraph.exists_dim o'.A o'.ab
  obtain ⟨l₁, l₂⟩ := m'.sq
  have C : GlobalTheory.AbDual.CupSquare (epsDP k) (GlobalTheory.DeRham.epsRed k) (o₀.A ⊗ o₀.A) :=
    GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod HR.1 HD.2 (isDPNilpotent_squareZero (SqExt.dual k).sq)
    (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl o'.ab hg' o'.ab hg' m'.cart m'.cart
  have iso : LBIso (o₀.P.pull (Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A)))) o₀.P :=
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB o₀.isLB _) o₀.isLB).1
      (by
        calc
          _ = GlobalTheory.CechPic.pull (Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A))) (GlobalTheory.CechPic.cls o₀.P o₀.isLB) := GlobalTheory.CechPic.cls_pull o₀.isLB _ _
          _ = _ := by rw [Over.id_left, GlobalTheory.CechPic.pull_id])
  obtain ⟨φ', hφ', e'⟩ := hφ.pull o₀.isLB (constMor o₀.A) (constMor o₀.A)
    (h := Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A))) (by simp) (by simp) o₀.isLB iso
  have van := GlobalTheory.BirigidLift.vanish_of_lift HR o'.ab hg' o'.ab hg' m'.cart m'.cart l₁ l₂ C o'.isLB o'.rig₁
    o'.rig₂ o₀.isLB (LBIso.symm m'.pol) hφ'
  have hm := GlobalTheory.HTRealise.isBC_constMor o₀.ab
  obtain ⟨xc, hxc⟩ := hm.exists x
  obtain ⟨yc, hyc⟩ := hm.exists y
  obtain ⟨x₁c, hx₁c⟩ := hm.exists x₁
  obtain ⟨y₁c, hy₁c⟩ := hm.exists y₁
  obtain ⟨d, hd, ed⟩ := hx
  obtain ⟨d', hd', ed'⟩ := hy
  have dx : d = xc + (DualNumber.eps : DualNumber k) • x₁c := GlobalTheory.HTRealise.crys_ext o₀.ab fun c ↦ by
    rw [ed c, LinearMap.add_apply, LinearMap.smul_apply, hxc c, hx₁c c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have dy : d' = yc + (DualNumber.eps : DualNumber k) • y₁c := GlobalTheory.HTRealise.crys_ext o₀.ab fun c ↦ by
    rw [ed' c, LinearMap.add_apply, LinearMap.smul_apply, hyc c, hy₁c c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have z : φ' d d' = 0 := van d hd d' hd'
  rw [dx, dy] at z
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    e' _ _ _ _ hxc hyc, e' _ _ _ _ hx₁c hyc, e' _ _ _ _ hxc hy₁c, e' _ _ _ _ hx₁c hy₁c] at z
  have z2 := congrArg TrivSqZeroExt.snd z
  simp [TrivSqZeroExt.algebraMap_eq_inl] at z2
  linear_combination z2

end GlobalTheory.HTSkew
