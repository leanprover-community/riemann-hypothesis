module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Mathlib.NumberTheory.NumberField.CMField
public import GroundTheory.AutomorphicForms.AdelicGLn
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap

@[expose] public section

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem exists_compact_open_level_le (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (S : Subgroup (GL (Fin N) (Af E))) (hS : IsOpen (S : Set (GL (Fin N) (Af E)))) :
    ∃ L : Subgroup (GL (Fin N) (Af E)), L ≤ S ∧ IsOpen (L : Set (GL (Fin N) (Af E))) ∧
      IsCompact (L : Set (GL (Fin N) (Af E))) := by
  let K : Subgroup (GL (Fin N) (Af E)) := GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E N
  have hKo : IsOpen (K : Set (GL (Fin N) (Af E))) :=
    GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E N
  have hKc : IsCompact (K : Set (GL (Fin N) (Af E))) :=
    GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E N
  have hSc : IsClosed (S : Set (GL (Fin N) (Af E))) := Subgroup.isClosed_of_isOpen S hS
  refine ⟨S ⊓ K, inf_le_left, ?_, ?_⟩
  · change IsOpen ((S : Set (GL (Fin N) (Af E))) ∩ (K : Set (GL (Fin N) (Af E))))
    exact hS.inter hKo
  · have : ((S ⊓ K : Subgroup _) : Set (GL (Fin N) (Af E))) =
        (K : Set (GL (Fin N) (Af E))) ∩ (S : Set (GL (Fin N) (Af E))) := by
      ext x; simp [and_comm]
    rw [this]
    exact hKc.inter_right hSc

end GlobalTheory.CompanionTheory.FinDiscOrth
