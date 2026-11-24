module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.CentralProd2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanContragredient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Exp.ThetaPf

open GlobalTheory.CompanionTheory.BZSegComm GlobalTheory.CompanionTheory.ThetaW

theorem thetaProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.Exp.ThetaProd k := by
  intro r t V W _ _ _ _ A B _ _
  obtain ⟨κ⟩ := ind₂_swap_equiv_comp_invT (k := k) (stdSum (rfl : r + t = r + t)) (stdSum (add_comm t r))
    (extTensor A B)
  obtain ⟨τ⟩ := nonempty_extTensor_swap (k := k) A B
  exact ⟨(compInvTEquiv (prod₂ A B)).symm.trans (κ.symm.trans
    (ind₂Equiv _ (τ.trans (extTensorCongr (compInvTEquiv B) (compInvTEquiv A)))))⟩

end PositivityTheory.RgUd.Exp.ThetaPf

end
