module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
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
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult
  MeasureTheory Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics

variable {D : D7}

abbrev Bas (V : HSp D) : Type := D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ

abbrev Pol (S T : HSp D) : Type := MvPolynomial (FVar D T.rank S.rank) ℂ

abbrev cmp (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : GA D V) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  infMat D.sp.cm.sig V.gram (θ τ) g

def StrictInterlace (n : ℕ) (A B : Finset ℚ) : Prop :=
  ∃ (a : Fin (n + 1) → ℚ) (b : Fin n → ℚ), A = Finset.univ.image a ∧ B = Finset.univ.image b ∧
    ∀ i : Fin n, b i < a i.castSucc ∧ a i.succ < b i

section Pair

variable (θ : InfFam D) {S T : HSp D} (BS : Bas S) (BT : Bas T) (e : D.what₂.Tau → ℚ)

def vacChar (g : GA D S) (h : GA D T) : ℂ :=
  ∏ τ, (cmp θ S τ g).det ^ ⌊e τ - (T.rank : ℚ) / 2⌋ * (cmp θ T τ h).det ^ (-⌊e τ - (S.rank : ℚ) / 2⌋)

def subst (g : GA D S) (h : GA D T) (x : FVar D T.rank S.rank) : Pol S T :=
  ∑ i, ∑ c, MvPolynomial.C (((BT x.1)⁻¹ * cmp θ T x.1 h * BT x.1) i x.2.1 * ((BS x.1)⁻¹ * cmp θ S x.1 g⁻¹ * BS x.1) x.2.2 c) *
    MvPolynomial.X (x.1, i, c)

def polAct (g : GA D S) (h : GA D T) : Pol S T →ₗ[ℂ] Pol S T :=
  vacChar θ e g h • (MvPolynomial.aeval (subst θ BS BT g h)).toLinearMap

variable (π : CoefA S) (π' : CoefA T)

end Pair

def fp (V : HSp D) (g : GA D V) : GfC V := ⟨GlobalTheory.LevelNbhd.finPartG V g, GlobalTheory.LevelNbhd.finPartG_mem_GfC V g⟩

section Global

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (BS : Bas S) (BT : Bas T)

variable {π : CoefA S} {π' : CoefA T}

end Global

section Last

variable {V A L : HSp D} (o : OrthDec V A L) (π : CoefA V) (δ : CoefA A)

end Last

section Chain

variable (P : TPar D) (θ : InfFam D) (X : ℕ → HSp D) {X' L : HSp D} (o : OrthDec (X D.R.m) X' L) (B : ∀ j, Bas (X j))

variable {X} (π : ∀ j, CoefA (X j))

variable (ψ : AddChar (AF D.host.F) ℂ) (om : ∀ j, Om (X j) (X (j + 1))) (f : ∀ j, WO (X j) (X (j + 1)) → ℂ)

variable (μ : ∀ j, Measure (GA D (X j))) (𝓕 : ∀ j, Set (GA D (X j)))



end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics

end
