module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceS
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatIntFMat
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualBIv
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceLatDualIiiOf
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitInt
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

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct



namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

theorem placeLatDual_of {D : D7} (hL : LatSelfDual D) : PlaceLatDual D := by
  intro ψ hψ S T ΛS ΛT hS hT
  refine ⟨fun e' he' u hu => latO_map_splitIdem S T ΛS ΛT he' hu,
    fun e' he' g h hg hh => PDB.placeLatDualVi D ψ hψ S T ΛS ΛT hS hT e' he' g h hg hh,
    fun P e he => ⟨PDA.placeLatDualIi_of hL ψ hψ S T ΛS ΛT hS hT P e he,
      PDA.placeLatDualIii_of hL ψ hψ S T ΛS ΛT hS hT P e he,
      PDB.placeLatDualIv D ψ hψ S T ΛS ΛT hS hT P e he,
      PDB.placeLatDualV D ψ hψ S T ΛS ΛT hS hT P e he⟩⟩

end Formalism.IndefR.Fin

end
