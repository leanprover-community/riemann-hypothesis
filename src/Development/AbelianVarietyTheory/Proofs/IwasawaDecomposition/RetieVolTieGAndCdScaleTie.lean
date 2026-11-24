module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Retie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueScaleIsScale
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesAgreeAdelicOfTrueVolumeStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.Vol GlobalTheory.Mem.Per

namespace GlobalTheory.Mem

theorem retie_volTieG_and_cdScaleTie :
    ∀ D : D7, Formalism.L2.Theta.VolTieG (retie D) ∧ cdScaleTie (retie D) := by
  intro D
  refine ⟨GlobalTheory.T.volumesAgreeAdelic_of_trueVolume (retie D) (fun _ => rfl), ?_⟩
  rw [cdScaleTie_iff]
  exact GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale D.cd

end GlobalTheory.Mem
