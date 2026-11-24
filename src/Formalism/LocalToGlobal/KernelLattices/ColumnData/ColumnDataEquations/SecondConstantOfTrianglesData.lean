module

public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNoEig
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.CharacterFactorUnitaryAction
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNormOne
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Cd.Base D cc δ}

theorem first_constant_of_triangles_data (hS : B.StdOK) (hL : B.LatAll) (hTL : Tr0L D B.tor) (hG : GaussRow B)
    (hLat : ∀ N N', Even N → Even N' → Lat0IsLat B N N') (hSp : ∀ N N', Even N → Even N' → B.ThZeroSpans N N') : J1 B := by
  intro N N' γ hN hN'
  obtain ⟨γ₁, γ₂, rfl, h1, h2⟩ := split_host D γ
  have h0 := Formalism.L2.Ker.Cd.Base.thZeroMem B hS N N'
  exact J1at_mul hL hTL hN hN' h0 γ₁ γ₂
    (J1at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₁ h1)
    (J1at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₂ h2)

theorem second_constant_of_triangles_data (hS : B.StdOK) (hL : B.LatAll) (hTR : Tr0R D B.tor) (hG : GaussRow B)
    (hLat : ∀ N N', Even N → Even N' → Lat0IsLat B N N') (hSp : ∀ N N', Even N → Even N' → B.ThZeroSpans N N') : J2 B := by
  intro N N' γ' hN hN'
  obtain ⟨γ₁, γ₂, rfl, h1, h2⟩ := split_host D γ'
  have h0 := Formalism.L2.Ker.Cd.Base.thZeroMem B hS N N'
  have key := J2at_mul hL hTR hN hN' h0 γ₁ γ₂
    (J2at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₁ h1)
    (J2at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₂ h2)
  have hhalf : B.thHalf N N' (StandardLatticesGL3.stdL D N) = B.thZero N N' := by
    unfold Formalism.L2.Ker.Cd.Base.thHalf
    exact iopSelf D B.tor N N' _ _ (Formalism.L2.Ker.Cd.mem_ThSp_of D B.tor _ _ h0)
  unfold J2at at key
  unfold Formalism.L2.Ker.Cd.Base.thMoved
  rw [hhalf]
  exact key

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
