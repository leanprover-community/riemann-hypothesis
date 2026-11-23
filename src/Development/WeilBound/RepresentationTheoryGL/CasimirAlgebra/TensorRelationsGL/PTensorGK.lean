module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.StepFormula
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGKA
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGKB
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGKC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

theorem tensorGK_of : TensorGl → TensorGK := by
  intro hT n M _ _ ι _ _ Γ _ _ bar κ E ρ hK hE P _ _ lab
  refine ⟨⟨fun τ => (hT n M P (E τ) (hE.gl τ) (fib lab τ)).1, fun τ τ' h a b c d => TGK.tE_comm E hE.comm lab τ τ' h a b c d,
    TGK.actT_one lab κ ρ hK.one hE.one, TGK.actT_mul lab κ ρ hK.mul hE.mul,
    fun γ τ a b => TGK.actT_ad lab κ E ρ hK.unit hE.ad γ τ a b, fun y => TGK.actT_fin lab κ ρ hE.fin y,
    fun y lam => TGK.actT_cont lab κ ρ hK.cont hE.cont y lam, ?_⟩,
    fun σ hσ γ => TGK.pm_actT lab κ ρ σ hσ γ⟩
  intro τ X hX
  obtain ⟨c, hc0, hd, hoth, hρ⟩ := hE.der τ X hX
  exact ⟨c, hc0, hd, hoth, fun y lam => TGK.actT_der lab κ E ρ bar τ (hK.ne τ) hE.one hK.one hK.conj X c hc0 hd hoth
    hρ y lam⟩

end PositivityTheory.Rg.Cz

end
