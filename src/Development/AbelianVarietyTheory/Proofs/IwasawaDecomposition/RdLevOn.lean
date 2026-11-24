module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.Adelic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfOfDecoRaw

@[expose] public section

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix

namespace GlobalTheory.SeeSaw.TwLev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def RatAt (Q : Finset (HeightOneSpectrum (𝓞 E))) : Set (GL (Fin n) (AfE F E)) :=
  {z | ∀ P : Q, ∀ i j, ∃ e : E, adAt F P.1 ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ e}

variable [StarRing E] {SG : Finset (HeightOneSpectrum (𝓞 E))}


variable (hc : CMData F E) in
def RdLevOn {K : Type} [Field K] (A : Set (GL (Fin n) (AfE F E))) (U : Subgroup (GL (Fin n) (AfE F E))) (chi : U →* ℂˣ)
    (Λ : LevFam E K n SG) (emb : K →+* ℂ) (Q : Finset (HeightOneSpectrum (𝓞 E)))
    (HQ : ∀ P : Q, Subgroup (GL (Fin n) (𝓞 E ⧸ P.1.asIdeal))) (lamQ : ∀ P : Q, HQ P →* ℂˣ) : Prop :=
  ∀ z ∈ A, ∀ hz : z ∈ St (1 : GL (Fin n) (AfE F E)), z ∈ UAd hc n →
    (z ∈ U ↔ (∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (Λ w).H) ∧ ∀ P : Q, redAt 1 P.1 ⟨z, hz⟩ ∈ HQ P) ∧
      ∀ (hU : z ∈ U) (h : ∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (Λ w).H) (h' : ∀ P : Q, redAt 1 P.1 ⟨z, hz⟩ ∈ HQ P),
        ((chi ⟨z, hU⟩ : ℂˣ) : ℂ) =
          (∏ w : SG, (emb (((Λ w).lam ⟨_, h w⟩ : Kˣ) : K))⁻¹) * ∏ P : Q, ((lamQ P ⟨_, h' P⟩ : ℂˣ) : ℂ)

end GlobalTheory.SeeSaw.TwLev
