module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptInDet
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.DotPTPinv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HacFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitLatticeBasisExists
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

theorem adaptIn_holds (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    AdaptIn X hb u p := by
  obtain ⟨θ, hθ, hε⟩ := exists_split_eps X p
  obtain ⟨P, hL⟩ := exists_GL_latBasis_of_isSplitEquiv X p θ hθ
  obtain ⟨o, hay, ho⟩ := adaptIn_ay X hb u p θ P hθ hL
  obtain ⟨hC, uu, huu, hdet⟩ := adaptIn_det X hb u p θ P hθ hε hL
  exact ⟨θ, hθ, P, hL, lF X u p θ, o, uu, fun s t hs ht => hac_frame X u p θ hθ s t hs ht, hay,
    fun s hs => (lF_unit X u p θ hb hθ s hs).1, fun s hs => (lF_unit X u p θ hb hθ s hs).2, ho, hC, huu, hdet⟩

theorem adapted_basis_every_place : AdaptInAll :=
  fun X hb _ u _ _ p => adaptIn_holds X hb u p

end PIW.MassDataColumns
