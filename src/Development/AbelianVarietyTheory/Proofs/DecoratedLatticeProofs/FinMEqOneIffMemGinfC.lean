module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem finM_eq_one_iff_mem_GinfC :
    ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V), finM V hn g = 1 ↔ g ∈ GinfC V := by
  intro D V n hn g
  subst hn
  have e0 : finM V rfl g = (Formalism.L2.Theta.mt V g).map (toEAf D) := by simp [finM]
  have e : (Formalism.L2.Theta.mt V g).map (toEAf D) = (finHom V g).val.map
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) := rfl
  rw [e0, e]
  constructor
  · intro h
    show finHom V g = 1
    apply Units.ext
    have hinj := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    apply Matrix.map_injective hinj
    show (finHom V g).val.map _ = (1 : Matrix _ _ _).map _
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  · intro hk
    have h : finHom V g = 1 := hk
    have h2 : (finHom V g).val = 1 := by rw [h]; rfl
    rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.AdForm
