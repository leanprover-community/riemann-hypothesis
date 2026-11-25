module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.Points
open GlobalTheory.GradedPieces
open GlobalTheory.CechPic (cls)

namespace GlobalTheory.LocM

section Graded

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure IntChart (Z : Mdl Y i₀) : Type where

  U : Z.X.Opens

  aff : IsAffineOpen U

  w : Vecs Dw (Y Z.i).t Γ(Z.X, U)

  int : IntFrame Z aff w

open Classical in
variable (Dw) in
def oneAt (σ : E →+* ℂ) (n : ℕ) (σ' : E →+* ℂ) (a : Fin (Dw.mult σ')) : ℤ := if σ' = σ ∧ (a : ℕ) = n then 1 else 0

variable {Z : Mdl Y i₀}

namespace IntChart

variable (c c' c'' : IntChart Z)

def vec {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) :
    TanM (x ≫ Z.π) (Y Z.i).t.G :=
  tanOf (tan_bc c.int (valMap x _ h).hom (spMap_valMap c.aff x h) σ a)

variable (hZ : HasDR Z)

def chg (σ : E →+* ℂ) : Fin (Dw.mult σ) → Fin (Dw.mult σ) → Γ(Z.X, c.U ⊓ c'.U) := (c.exists_tri c' hZ σ).choose

def tr (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : Γ(Z.X, c.U ⊓ c'.U)ˣ :=
  ∏ σ, ∏ a, (c.isUnit_chg c' hZ σ a).unit ^ e σ a

end IntChart

variable (hZ : HasDR Z) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ)

def grLB : LB Z.X := ⟨IntChart Z, IntChart.U, fun c c' => c.tr c' hZ e⟩

def grCls : (∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) →+ CechPic.Pic Z.X :=
  AddMonoidHom.mk' (fun e => cls _ (isLB_grLB hZ e)) fun e e' => by
    have h := CechPic.isLB_tens (isLB_grLB hZ e) (isLB_grLB hZ e')
    refine (CechPic.cls_eq_iff _ h).2 (CechPic.iso_of_chart h ⟨fun c => (c, c), fun _ _ h => ⟨h, h⟩, fun y c c' hc hc' => ?_⟩)
    refine .trans ?_ (CechPic.gm_tens (grLB hZ e) (grLB hZ e') (𝟙 _) y (c, c) (c', c') ⟨hc, hc⟩ ⟨hc', hc'⟩).symm
    exact (congrArg _ (IntChart.tr_add c c' hZ e e')).trans (map_mul _ _ _)

end Graded

section Curves

structure Curve (k : Type) [Field k] (X : Scheme.{0}) : Type where

  n : ℕ

  I : (PSpace k n).IdealSheafData

  integral : IsIntegral I.subscheme

  dim : topologicalKrullDim I.subscheme = 1

  smooth : Smooth (I.subschemeι ≫ PSpace.str k n)

  f : I.subscheme ⟶ X

namespace Curve

variable {k : Type} [Field k] {X : Scheme.{0}} (c : Curve k X)

abbrev C : Scheme.{0} := c.I.subscheme

instance : IsIntegral c.C := c.integral

instance algebra : Algebra k Γ(c.C, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (c.I.subschemeι ≫ PSpace.str k c.n).appTop).hom.toAlgebra

def degPic : CechPic.Pic X →+ ℤ := c.isProjCurve.degPic.comp (CechPic.pull c.f)

end Curve

end Curves

section OnModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} {k : Type} [Field k] (c : Curve k Z.X)

namespace Curve

def t : SAB H c.C := (exists_sab (c.f ≫ Z.π) (Y Z.i).t).choose

def tMap : SABMap c.t (Y Z.i).t (c.f ≫ Z.π) := (exists_sab (c.f ≫ Z.π) (Y Z.i).t).choose_spec.some

abbrev lie : c.C.Modules := LieVB.Lie c.t.G

def eDeg : ℤ := -VB.deg k c.lie

def Pm : ℤ := sSup (VB.subDegs k c.lie)

variable (hZ : HasDR Z)

def degGr : (∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) →+ ℤ := c.degPic.comp (grCls hZ)

def degStep (σ : E →+* ℂ) (n : ℕ) : ℤ := c.degGr hZ (-oneAt Dw σ n)

end Curve

end OnModel

section Place

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

def Fbar (ct : At S κ p) : Type := haveI := Fact.mk ct.hp; AlgebraicClosure (ZMod p)

instance : Field ct.Fbar := haveI := Fact.mk ct.hp; inferInstanceAs (Field (AlgebraicClosure (ZMod p)))

abbrev Crv : Type := Curve ct.Fbar ct.YY.X

abbrev CrvQ : Type := Curve (AlgebraicClosure κ.c.F) ct.YY.X

open Classical in
def indWt (τ : PsiT D) (i : ℕ) : PsiT D → ℕ → ℤ := fun τ' i' => if τ' = τ ∧ i' = i then 1 else 0

def degPiece {k : Type} [Field k] (c : Curve k ct.YY.X) (τ : PsiT D) (i : ℕ) : ℤ :=
  c.degGr ct.hasDR (-ct.expo (indWt τ i))

def degLie {k : Type} [Field k] (c : Curve k ct.YY.X) (τ : PsiT D) : Bool → ℤ
  | false => ∑ i ∈ Finset.Icc 1 j, ct.degPiece c τ i
  | true => -∑ i ∈ Finset.Icc (j + 1) N, ct.degPiece c τ i

def degWt {k : Type} [Field k] (c : Curve k ct.YY.X) (l : PsiT D → ℕ → ℝ) : ℝ :=
  -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 N, l τ i * (ct.degPiece c τ i : ℝ)

def nefQ (l : PsiT D → ℕ → ℝ) : Prop := ∀ c : ct.CrvQ, 0 ≤ ct.degWt c l

end At

def embOf (D : D7) (τ : PsiT D) : D.host.E →+* ℂ := DV.tauEmb D (D.eTau.symm τ)

end Place

end GlobalTheory.LocM
