module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IdentityOnLastEmbedding
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaEps
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaLine
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.ParabolicThetaScalar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.SubMulRight
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.VacCut
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.EmEqInr

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open GlobalTheory.Doubling (absE)

theorem iwaQ_of' (hT : TAll) : IwaQ := by
  intro F E _ _ _ _ _ σ d L x
  obtain ⟨p, k, lam, hk, rfl, hp⟩ := line_fix' L.i₀ x
  obtain ⟨ε, hd, hL⟩ := eps_eq L
  obtain ⟨g, hq⟩ := q_split' L ε hd hL p lam hp
  set q := p * (L.j g)⁻¹ with hqdef
  obtain ⟨c, hc⟩ := parabolic_theta_scalar hT L.i₀ hq
  refine ⟨q, g, k, (absE F E lam : ℝ), c, hk, by simp [hqdef, mul_assoc], absE_pos lam, fun g' => ?_, fun Φ hΦ g' X hX => ?_⟩
  · have e : L.j g' * (p * k) = (L.j g' * q * (L.j g')⁻¹) * L.j (g' * g) * k := by
      simp only [hqdef, map_mul, mul_assoc, inv_mul_cancel_left]
    rw [e, KWhit.a_mul_K d _ k hk, q_ht' L (q_conj' L hq g') (g' * g)]
  · set Ψ := d.om q Φ - c • Φ with hΨ
    have hΨs : Ψ ∈ d.sch := sub_mem (KWhit.om_mem_sch d q hΦ) (Submodule.smul_mem _ c hΦ)
    have hTΨ : ∀ X : Mx F E d.m d.n, (∀ a, X a L.i₀ = 0) → d.T Ψ X = 0 := by
      intro X hX
      have := (Tl d).map_sub (d.om q Φ) (c • Φ)
      have hs := (Tl d).map_smul c Φ
      simp only [Tl, LinearMap.coe_mk, AddHom.coe_mk] at this hs
      rw [hΨ, this, hs, Pi.sub_apply, Pi.smul_apply, hc Φ hΦ X hX, smul_eq_mul, sub_self]
    have key := L.res Ψ hΨs 0 (zero_mem _) (fun X hX => by rw [T_zero, hTΨ X hX]; rfl) g' X hX
    rw [map_zero, T_zero] at key
    have e1 : d.om (L.j g') Ψ = d.om (L.j g') (d.om q Φ) - c • d.om (L.j g') Φ := by
      rw [hΨ, map_sub, map_smul]
    have e2 := congrFun ((Tl d).map_sub (d.om (L.j g') (d.om q Φ)) (c • d.om (L.j g') Φ)) X
    have e3 := congrFun ((Tl d).map_smul c (d.om (L.j g') Φ)) X
    simp only [Tl, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e2 e3
    rw [map_mul, Module.End.mul_apply]
    have : d.T (d.om (L.j g') Ψ) X = 0 := key.symm
    rw [e1, e2, e3] at this
    exact sub_eq_zero.1 this

end PositivityTheory.SiegelWeilFormula.Avac

end
