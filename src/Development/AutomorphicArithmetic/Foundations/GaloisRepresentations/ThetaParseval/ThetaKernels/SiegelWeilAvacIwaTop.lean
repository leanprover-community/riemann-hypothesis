module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaB
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaCut
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaE
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaEps
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaLine
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacVacCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
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

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open GlobalTheory.Doubling (absE)
theorem iwaQ_of'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : _root_.PositivityTheory.SiegelWeilFormula.IwaQ_k := by
  intro F E _ _ _ _ _ σ d L x
  obtain ⟨p, k, lam, hk, rfl, hp⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.line_fix'_k L.i₀ x
  obtain ⟨ε, hd, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.eps_eq_k L
  obtain ⟨g, hq⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.q_split'_k L ε hd hL p lam hp
  set q := p * (L.j g)⁻¹ with hqdef
  obtain ⟨c, hc⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.q_T'_k hT L.i₀ hq
  refine ⟨q, g, k, (absE F E lam : ℝ), c, hk, by simp [hqdef, mul_assoc], absE_pos lam, fun g' => ?_, fun Φ hΦ g' X hX => ?_⟩
  · have e : L.j g' * (p * k) = (L.j g' * q * (L.j g')⁻¹) * L.j (g' * g) * k := by
      simp only [hqdef, map_mul, mul_assoc, inv_mul_cancel_left]
    rw [e, _root_.PositivityTheory.SiegelWeilFormula.KWhit.a_mul_K_k d _ k hk, _root_.PositivityTheory.SiegelWeilFormula.Avac.q_ht'_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.q_conj'_k L hq g') (g' * g)]
  · set Ψ := d.om q Φ - c • Φ with hΨ
    have hΨs : Ψ ∈ d.sch := sub_mem (_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d q hΦ) (Submodule.smul_mem _ c hΦ)
    have hTΨ : ∀ X : Mx F E d.m d.n, (∀ a, X a L.i₀ = 0) → d.T Ψ X = 0 := by
      intro X hX
      have := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_sub (d.om q Φ) (c • Φ)
      have hs := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_smul c Φ
      simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k, LinearMap.coe_mk, AddHom.coe_mk] at this hs
      rw [hΨ, this, hs, Pi.sub_apply, Pi.smul_apply, hc Φ hΦ X hX, smul_eq_mul, sub_self]
    have key := L.res Ψ hΨs 0 (zero_mem _) (fun X hX => by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.T_zero_k, hTΨ X hX]; rfl) g' X hX
    rw [map_zero, _root_.PositivityTheory.SiegelWeilFormula.Avac.T_zero_k] at key
    have e1 : d.om (L.j g') Ψ = d.om (L.j g') (d.om q Φ) - c • d.om (L.j g') Φ := by
      rw [hΨ, map_sub, map_smul]
    have e2 := congrFun ((_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_sub (d.om (L.j g') (d.om q Φ)) (c • d.om (L.j g') Φ)) X
    have e3 := congrFun ((_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_smul c (d.om (L.j g') Φ)) X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e2 e3
    rw [map_mul, Module.End.mul_apply]
    have : d.T (d.om (L.j g') Ψ) X = 0 := key.symm
    rw [e1, e2, e3] at this
    exact sub_eq_zero.1 this
end PositivityTheory.SiegelWeilFormula.Avac
end
end
