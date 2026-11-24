module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section



section
noncomputable section
namespace Formalism.MainNotions.PairedCharacterCondition
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Module Polynomial
variable {D : D7}
def PairedCharacterConditionAlt (C : ℝ) (CT : ℕ) : Prop :=
  ∀ (i : D.nd.Loc) (k k' : Fin 2), k ≠ k' → D.nd.l i = D.host.g k →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
    GoodR D.nd i r → (∀ π ∈ D.nd.Z i, Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) →
  ∀ (eta s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool)
    (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ),
    eta + D.R.t + 1 < s →
    Real.log (D.host.g k' : ℝ) ≤ 2 * Real.log (D.host.g k : ℝ) →
    CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k →
    SignOK i sg → HostJ i r eta s S sg U → (∀ π ∈ D.nd.Zgood i, Br.sFin D.loc D.nbr i ρ π) →
    (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
    (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ) * rhs C eta i ρ π
def GaloisFamilyConditions' : Prop :=
  ∀ i r, GoodR D.nd i r →
    Formalism.MainNotions.SumRepresentations.At.G1 D.nd i r ∧ _root_.UpperTheory.GalS.G2a D.nd D.naut i r ∧ _root_.UpperTheory.GalS.G3 D.nd i r ∧
      Formalism.MainNotions.SumRepresentations.At.G4 D.nd i r
def LocalGlobalCompatibility' : Prop := _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D
section Pending
end Pending
end Formalism.MainNotions.PairedCharacterCondition
end
end
