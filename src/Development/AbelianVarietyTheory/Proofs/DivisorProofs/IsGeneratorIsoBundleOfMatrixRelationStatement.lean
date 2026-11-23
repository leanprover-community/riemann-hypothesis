module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGeneratorIsoBundleOfMatrixRelation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.isGenerator_isoBundle_of_matrix_relation : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (R : Type) [CommRing R] (A' B' : Over (Sp R)) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)ˣ), GlobalTheory.HomFixUniv.Generates bA ψA A'.hom c → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (c i j) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → (⟨u⟩ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)).IsGen := by
  first | (exact @GlobalTheory.HomFixUniv.isGen_of_matRel) | (exact GlobalTheory.HomFixUniv.isGen_of_matRel) | (intros; apply GlobalTheory.HomFixUniv.isGen_of_matRel  <;> assumption)
