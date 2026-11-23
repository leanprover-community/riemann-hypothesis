module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeIndexSplitPlaceEqProductLocal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke GlobalTheory.RawLift
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lattice_index_split_place_eq_product_local : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (W : HSp D) (β : GL (Fin W.rank) (Fv D.host.F v)), Frame W e π β → ∀ g : GA D W, SuppAt e W g → latIndex W g = ((Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).map ((((rho W π β g : GL (Fin W.rank) (Fv D.host.F v)) : Matrix (Fin W.rank) (Fin W.rank) (Fv D.host.F v)).mulVecLin).restrictScalars (Ov D v))).toAddSubgroup.relIndex (Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).toAddSubgroup * ((Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).map ((((rho W π β g⁻¹ : GL (Fin W.rank) (Fv D.host.F v)) : Matrix (Fin W.rank) (Fin W.rank) (Fv D.host.F v))ᵀ.mulVecLin).restrictScalars (Ov D v))).toAddSubgroup.relIndex (Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).toAddSubgroup := by
  first | exact @GlobalTheory.SplitIndexLocal.latIndex_split_local | exact GlobalTheory.SplitIndexLocal.latIndex_split_local | (intros; apply GlobalTheory.SplitIndexLocal.latIndex_split_local <;> assumption)
