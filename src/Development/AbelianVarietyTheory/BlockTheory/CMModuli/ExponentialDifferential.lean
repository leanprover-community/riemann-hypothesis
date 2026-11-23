module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Mathlib.Analysis.CStarAlgebra.Classes
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real

namespace GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms

def In {R : Type} [CommRing R] {X : Scheme.{0}} (x : Sp R ⟶ X) (U : X.Opens) : Prop :=
  (⊤ : (Sp R).Opens) ≤ x ⁻¹ᵁ U

def val {R : Type} [CommRing R] {X : Scheme.{0}} (x : Sp R ⟶ X) {U : X.Opens} (h : In x U)
    (f : Γ(X, U)) : R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((x.appLE U ⊤ h).hom f)

abbrev Pt (A : Over (Sp ℂ)) : Type := 𝟙_ (Over (Sp ℂ)) ⟶ A

abbrev Pt.mor {A : Over (Sp ℂ)} (x : Pt A) : Sp ℂ ⟶ A.left := x.left

abbrev EpsPt (A : Over (Sp ℂ)) : Type := epsPt (𝟙 (Sp ℂ)) ⟶ A

abbrev EpsPt.mor {A : Over (Sp ℂ)} (v : EpsPt A) : Sp (DualNumber ℂ) ⟶ A.left := v.left


open Classical in
def extZero {V : Type} (s : Set V) (F : ∀ z, z ∈ s → ℂ) : V → ℂ :=
  fun z => if h : z ∈ s then F z h else 0

section Hol

variable {g : ℕ} {A : Over (Sp ℂ)}

def pre (u : (Fin g → ℂ) → Pt A) (U : A.left.Opens) : Set (Fin g → ℂ) := {z | In (u z).mor U}

def comp (u : (Fin g → ℂ) → Pt A) (U : A.left.Opens) (f : Γ(A.left, U)) : (Fin g → ℂ) → ℂ :=
  extZero (pre u U) (fun z h => val (u z).mor h f)

def IsHol (u : (Fin g → ℂ) → Pt A) : Prop :=
  ∀ U : A.left.Opens, IsOpen (pre u U) ∧ ∀ f : Γ(A.left, U), DifferentiableOn ℂ (comp u U f) (pre u U)

variable [GrpObj A]

def IsTangent (v : EpsPt A) : Prop :=
  spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.mor = (1 : Pt A).mor

def IsDiffAt (u : (Fin g → ℂ) → Pt A) (w : Fin g → ℂ) (v : EpsPt A) : Prop :=
  IsTangent v ∧ ∀ (U : A.left.Opens) (h : In v.mor U) (f : Γ(A.left, U)),
    HasDerivAt (fun t : ℂ => comp u U f (t • w)) (val v.mor h f).snd 0

end Hol

structure Exp (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) where
  exp : (Fin g → ℂ) → Pt A
  exp_add : ∀ z z', exp (z + z') = exp z * exp z'
  hol : IsHol exp
  onto : Function.Surjective exp
  locIso : ∀ v : EpsPt A, IsTangent v → ∃! w, IsDiffAt exp w v
  discrete : DiscreteTopology {z : Fin g → ℂ | exp z = 1}
  span : Submodule.span ℝ {z : Fin g → ℂ | exp z = 1} = ⊤

namespace Exp

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (E : Exp A g)

def hom : Multiplicative (Fin g → ℂ) →* Pt A :=
  MonoidHom.mk' (fun z => E.exp z.toAdd) (fun _ _ => E.exp_add _ _)

end Exp

structure Unif (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) extends Exp A g where
  isLB : L.IsLB
  fr : ∀ (i : L.ι) (z : Fin g → ℂ), z ∈ pre exp (L.U i) → ℂ
  fr_ne : ∀ i z h, fr i z h ≠ 0
  fr_hol : ∀ i, DifferentiableOn ℂ (extZero (pre exp (L.U i)) (fr i)) (pre exp (L.U i))
  fr_compat : ∀ (i j : L.ι) (z : Fin g → ℂ) (hi : z ∈ pre exp (L.U i)) (hj : z ∈ pre exp (L.U j))
    (hij : In (exp z).mor (L.U i ⊓ L.U j)),
    fr i z hi = val (exp z).mor hij (L.g i j : Γ(A.left, L.U i ⊓ L.U j)) * fr j z hj

structure AHDatum {g : ℕ} (La : Submodule ℤ (Fin g → ℂ)) where
  H : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) →ₗ⋆[ℂ] ℂ
  herm : ∀ x y, H y x = starRingEnd ℂ (H x y)
  pos : ∀ x, x ≠ 0 → 0 < (H x x).re
  integral : ∀ la mu : La, ∃ n : ℤ, (H la mu).im = n
  ch : La → ℂ
  ch_norm : ∀ la, ‖ch la‖ = 1
  ch_add : ∀ la mu : La,
    ch (la + mu) = ch la * ch mu * Complex.exp (π * Complex.I * ((H la mu).im : ℝ))

def AHDatum.factor {g : ℕ} {La : Submodule ℤ (Fin g → ℂ)} (D : AHDatum La) (la : La) (z : Fin g → ℂ) : ℂ :=
  D.ch la * Complex.exp (π * D.H z la + π * D.H la la / 2)

namespace Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (F : Unif A L g)

end Unif

def e (x : ℂ) : ℂ := Complex.exp (2 * π * Complex.I * x)

def Siegel (g : ℕ) : Type :=
  {τ : Matrix (Fin g) (Fin g) ℂ // τ.IsSymm ∧ (τ.map Complex.im).PosDef}

def thetaTerm {g : ℕ} (a b : Fin g → ℝ) (z : Fin g → ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) (l : Fin g → ℤ) : ℂ :=
  e ((∑ i, ∑ j, ((l i : ℂ) + a i) * τ i j * ((l j : ℂ) + a j)) / 2 + ∑ i, ((l i : ℂ) + a i) * (z i + b i))

def theta {g : ℕ} (a b : Fin g → ℝ) (z : Fin g → ℂ) (τ : Siegel g) : ℂ :=
  ∑' l : Fin g → ℤ, thetaTerm a b z τ.1 l

end GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms
