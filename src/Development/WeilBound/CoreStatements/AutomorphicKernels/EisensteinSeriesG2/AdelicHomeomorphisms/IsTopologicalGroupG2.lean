module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.EisBL.AETop

open NumberField IsDedekindDomain Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance fdAE : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

instance modTopAE : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩

instance ringAE : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem nonempty_homeomorphAE : Nonempty (AE F E ≃ₜ (Fin (Module.finrank F E) → AF F)) :=
  GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)

instance t2AE : T2Space (AE F E) := by
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := nonempty_homeomorphAE (F := F) (E := E)
  exact e.isEmbedding.t2Space

instance locCompactAE : LocallyCompactSpace (AE F E) := by
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  obtain ⟨e⟩ := nonempty_homeomorphAE (F := F) (E := E)
  exact e.isClosedEmbedding.locallyCompactSpace

instance secondCountableAE : SecondCountableTopology (AE F E) := by
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e⟩ := nonempty_homeomorphAE (F := F) (E := E)
  exact e.secondCountableTopology

instance topGrpGL {ι : Type} [Fintype ι] [DecidableEq ι] : IsTopologicalGroup (GL ι (AE F E)) := inferInstance

instance isTopologicalGroup_G2 {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} : IsTopologicalGroup (G2 σ Y) := inferInstance

end GlobalTheory.EisBL.AETop
