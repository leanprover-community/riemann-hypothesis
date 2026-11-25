module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernIntegralEqDegree
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact
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
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.LB (resG_resG resG_self toMod)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open MeasureTheory
open scoped ContDiff ComplexOrder ENNReal

namespace GlobalTheory

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ σ' : k →+* ℂ}

namespace Met

variable {E F : X.Modules} {r s : ℕ} (h : Met p σ E r) {U : X.Opens} {y : CxPts p σ} {ι : Type}

def gram (t : ι → Γ(E, U)) (y : CxPts p σ) : Matrix ι ι ℂ := Matrix.of fun a b => h.form (t a) (t b) y

end Met

namespace VBExt.AdaptedChart

variable {S : ShortComplex X.Modules} {r s : ℕ} (hS : S.ShortExact) (a a' : AdaptedChart S r s)
  {U : X.Opens} {y : CxPts p σ}

def sub : Chart S.X₁ r := ⟨a.U, a.e, a.he⟩

def quot : Chart S.X₃ s := ⟨a.U, _, a.ht⟩

def frame : Fin r ⊕ Fin s → Γ(S.X₂, a.U) := Sum.elim (fun i => S.f.app a.U (a.e i)) a.t

def mid : Chart S.X₂ (r + s) :=
  ⟨a.U, a.frame ∘ finSumFinEquiv.symm,
    (isFrame_sumElim hS a.he a.ht).comp_equiv finSumFinEquiv.symm⟩

variable (p σ) in
def tr (y : CxPts p σ) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ :=
  ((a.mid hS).tr p σ (a'.mid hS) y).submatrix finSumFinEquiv finSumFinEquiv

end VBExt.AdaptedChart

namespace Met

variable {S : ShortComplex X.Modules} {r s : ℕ} (h : Met p σ S.X₂ (r + s)) (hS : S.ShortExact)
  (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) {y : CxPts p σ} (a a' : AdaptedChart S r s)

def quot : Met p σ S.X₃ s :=
  ofCover h₃ AdaptedChart.quot (exists_adapted hS h₁ h₃) (fun a y => quotGram (h.gram a.frame y))
    fun a _ hy => posDef_quotGram (h.posDef_gram_frame hS a hy)

end Met

namespace Met

variable {E F : X.Modules} {r s : ℕ} (h : Met p σ E r) {i : F ⟶ E}

variable {h}

end Met

namespace Met

variable {S : ShortComplex X.Modules} {r s : ℕ} (h : Met p σ S.X₂ (r + s)) (hS : S.ShortExact)
  (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) {y : CxPts p σ} (a a' : AdaptedChart S r s)
  {D : ℕ} (c c' : AlgChart p σ D)

variable {h}

variable (h) (c c' : AlgChart p σ 1)

variable {h}

end Met

namespace VMetric

section Seq

variable {S : ShortComplex X.Modules} {r s : ℕ} (h : VMetric p S.X₂ (r + s)) (hS : S.ShortExact)
  (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s)

def quot : VMetric p S.X₃ s :=
  ⟨h₃, fun σ => (h.met σ).quot hS h₁ h₃, fun σ σ' => (h.conj σ σ').quot hS h₁ h₃⟩

end Seq

variable {E F : X.Modules} {r s : ℕ} (h : VMetric p E r)

variable (fl : Vert.Flag E r) (i : Fin r)

abbrev stepSeq : ShortComplex X.Modules := .mk (fl.step i) (fl.π i) (Limits.cokernel.condition _)

end VMetric

end GlobalTheory
