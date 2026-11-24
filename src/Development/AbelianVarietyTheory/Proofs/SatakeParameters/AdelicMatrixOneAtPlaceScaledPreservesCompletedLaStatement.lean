module

public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicMatrixOneAtPlaceScaledPreservesCompletedLa
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
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.UG (bc prV)
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.adelicMatrix_one_at_place_scaled_preserves_completedLattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), bc (prV (E := E) v) k = 1 →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Lb,
      Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) •
        ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z) ∈ Formalism.L2.Herm.hatL (F := F) Lb := by
  first | exact @GlobalTheory.AwayScale.main | exact GlobalTheory.AwayScale.main | (intros; apply GlobalTheory.AwayScale.main <;> assumption)
