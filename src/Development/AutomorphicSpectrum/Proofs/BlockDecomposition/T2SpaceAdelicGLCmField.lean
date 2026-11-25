module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAdelicFourierSeparatingCharsVanish
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwConjOfIsTest
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralTsumEnormNeTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFCA
import GroundTheory.AutomorphicForms.AdelicGLn
import GroundTheory.GlobalFields.Adele.Topology
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.UnfoldCut

section Measure

variable {D G : Type} [Group D] [Group G]

def hh (S : Set G) (θ : Monoid.End G) (ι : D →* G) (φ : G → ℂ) (x : G) (d : D) : ℂ :=
  S.indicator (1 : G → ℂ) x * φ (twConj θ x (ι d))

def twEquiv (θD : Monoid.End D) (g : D) : D ≃ D where
  toFun := twConj θD g
  invFun := twConj θD g⁻¹
  left_inv d := by rw [← twConj_mul']; simp [twConj]
  right_inv d := by rw [← twConj_mul']; simp [twConj]

end Measure

section Top

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem secondCountable_GA : SecondCountableTopology (GA E n) := by
  haveI := _root_.GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI : SecondCountableTopology (Ad E) :=
    inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem locallyCompact_GA : LocallyCompactSpace (GA E n) :=
  GroundTheory.Automorphic.AdelicGLn.locallyCompactSpace E n

theorem t2Space_adelicGL_cmField : T2Space (GA E n) := by
  haveI := _root_.GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  haveI : T2Space (Ad E) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))
  haveI : T2Space (Matrix (Fin n) (Fin n) (Ad E)) :=
    inferInstanceAs (T2Space (Fin n → Fin n → Ad E))
  haveI : T2Space (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.t2Space
  exact Units.isEmbedding_embedProduct.t2Space

theorem countable_GL : Countable (GL (Fin n) E) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Units.val_injective.countable

end Top

end GlobalTheory.CompanionTheory.UnfoldCut

end
