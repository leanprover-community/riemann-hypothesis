module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.ThetaOfCsdR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedHolds2
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatAsc
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

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

theorem spehExp_injective (d : ℕ) : Function.Injective (spehExp d) := fun i j h => by
  have h' : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
    unfold spehExp at h
    linarith
  exact Fin.ext (by exact_mod_cast h')

theorem strSat : StrSat := by
  intro E _ _ _ N a d V P σ hN hV hPu hPn hA hloc ν hν
  have hd : 1 ≤ d := by
    obtain ⟨hsum, -⟩ := hA
    rcases Nat.eq_zero_or_pos d with rfl | h
    · simp at hsum
      omega
    · exact h
  have hex : ∀ s : ℝ, ∃ χ : Formalism.L2.Host.HChar E, χ.IsAbsPow s :=
    fun s => ⟨_, GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s⟩
  choose χ0 hχ0 using hex
  classical
  let μ : ℝ → Formalism.L2.Host.HChar E := fun s =>
    if h : ∃ k, spehExp d k = s then ν h.choose else χ0 s
  have hμ : ∀ s, (μ s).IsAbsPow s := fun s => by
    by_cases h : ∃ k, spehExp d k = s
    · simp only [μ, dif_pos h]
      have := hν h.choose
      rwa [h.choose_spec] at this
    · simp only [μ, dif_neg h]
      exact hχ0 s
  have hμk : ∀ k, μ (spehExp d k) = ν k := fun k => by
    have h : ∃ k', spehExp d k' = spehExp d k := ⟨k, rfl⟩
    simp only [μ, dif_pos h]
    rw [spehExp_injective d h.choose_spec]
  filter_upwards [GlobalTheory.SpehPair.eventually_spherical hV] with w hw
  have hsph := hw (σ w) (hloc w)
  obtain ⟨T, hT⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible (σ w).smooth (σ w).irred hsph
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E a P w
  have hS := PositivityTheory.Rg.Rs.ascSeed_holds2.2 E N a d V P hN hV hPu hPn hA w τ (σ w) hτ (hloc w)
  obtain ⟨B, hB, hBT⟩ := GlobalTheory.SpehPair.exists_sat_twist hd hτ hS hT μ hμ
  have hsum : ∑ k : Fin d, B k.rev = T := by
    rw [← hBT]
    exact Fintype.sum_equiv Fin.revPerm _ _ fun _ => rfl
  refine ⟨fun k => B k.rev, fun k => ?_, hsph, hsum ▸ hT⟩
  have := hB k.rev
  rwa [PositivityTheory.Rg.Rs.satakeAscent.spehExp_rev, neg_neg, hμk, CG.twist_mk] at this

end PositivityTheory.Rg.BcB.F.Rig

end
