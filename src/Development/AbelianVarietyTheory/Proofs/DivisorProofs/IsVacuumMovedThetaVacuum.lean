module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeTransportPreservesSelfDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.MovedVacuum

theorem isVacuum_thetaIntertwiner_selfDual (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl t0 : ℂ) (hc : StandardLatticesGL3.Crv D cc dl)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0) {a b : ℕ}
    {L L₁ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' L₁' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (hL : StandardLatticesGL3.SD D L) (hL' : StandardLatticesGL3.SD D L') (hL₁ : StandardLatticesGL3.SD D L₁) (hL₁' : StandardLatticesGL3.SD D L₁')
    {G : TaylorLogMetric.VC D a b → ℂ} (hG : StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' G) :
    StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L₁ L₁'
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc dl) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc dl) L L')
        (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc dl) L₁ L₁') G) := by
  obtain ⟨e, κ, he, hκ, rfl⟩ := hG
  obtain ⟨μ, hμ, h⟩ := GlobalTheory.TripleIntertwiner.triple_constant D cc dl hc a b _ _ _
    (Or.inl ⟨_, e, he, rfl⟩) (Or.inr ⟨L, L', hL, hL', rfl⟩) (Or.inr ⟨L₁, L₁', hL₁, hL₁', rfl⟩) _
    (GlobalTheory.VacuumMove.pullbackOrthonormal_normalizedTheta_mem_thetaSpace D (GlobalTheory.InducedType.induced_type D).1 cc dl t0 hc ht e he.1)
  refine ⟨e, κ * μ, he, GlobalTheory.VacuumMove.mod1All_mul hκ hμ, funext fun z => ?_⟩
  rw [GlobalTheory.VacuumMove.Iop_mul, mul_assoc κ μ]
  exact congrArg (κ * ·) (congrFun h z)

theorem sd_stdL (D : D7) (n : ℕ) : StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D n) := by
  letI := D.host.cmStar
  exact GlobalTheory.SeamSelfDual.isSDLat_pi D.host.E n

theorem isVacuum_movedThetaVacuum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) (B.thZero a b) → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' (B.thMoved a b L L') := by
  intro D cc dl B t0 hc ht a b L L' hL hL' h0
  exact isVacuum_thetaIntertwiner_selfDual D cc dl t0 hc ht hL (sd_stdL D b) hL hL'
    (isVacuum_thetaIntertwiner_selfDual D cc dl t0 hc ht (sd_stdL D a) (sd_stdL D b) hL (sd_stdL D b) h0)

end GlobalTheory.MovedVacuum
