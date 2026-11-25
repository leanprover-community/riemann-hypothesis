module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Prelims.UnramifiedAntiInvariantLocal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
/-! # ExistsLocUnit: Preliminary helper declarations for global theta kernels. -/

@[expose] public section

private theorem inv_mem {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (n : NumberField.RingOfIntegers F) (hn : n ∉ v.asIdeal) :
    algebraMap F (v.adicCompletion F) (n : F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : v.valuation F (n : F) = 1 := by
    have := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) v (r := n)).2 hn
    exact this
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((n : F)⁻¹)
  refine le_of_eq (Eq.trans h2 ?_)
  rw [map_inv₀, h1, inv_one]

theorem UpperTheory.Reformulated.B.Gs6.exists_locUnit :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {σ : E →ₐ[F] E} {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E},
      UpperTheory.TP.W.GoodK σ B →
        ∀ {ξ : E},
          ξ ≠ (0 : E) →
            (σ : E → E) ξ = -ξ →
              ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
                ∃ (u : (TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E)ˣ),
                  (↑u : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E) ∈ GlobalTheory.AdelicU.intLoc F E v ∧
                    (↑u⁻¹ : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E) ∈ GlobalTheory.AdelicU.intLoc F E v ∧
                      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ :
                                  TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E)
                                (↑u : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E) =
                        -(↑u : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E) := by
  intro F E _ _ _ _ _ σ B hG ξ hξ hσ v
  obtain ⟨hCM, -, hU, -, -, -⟩ := hG
  obtain ⟨a, b, n, hn, ha, hab⟩ := UpperTheory.unramified_anti_invariant_local σ hCM.2.2.1 hU ξ hξ hσ v
  have hn0 : (n : F) ≠ 0 := by
    intro h
    apply hn
    have : n = 0 := by exact_mod_cast h
    rw [this]; exact v.asIdeal.zero_mem
  have hmul : ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (a : E)) *
      (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (n : F)⁻¹ ⊗ₜ[F] (b : E)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, hab, one_mul, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul_smul, inv_mul_cancel₀ hn0, one_smul]
    rfl
  refine ⟨⟨_, _, hmul, by rw [mul_comm]; exact hmul⟩, ?_, ?_, ?_⟩
  · exact AddSubgroup.subset_closure ⟨1, one_mem _, a, rfl⟩
  · exact AddSubgroup.subset_closure ⟨_, inv_mem v n hn, b, rfl⟩
  · change Algebra.TensorProduct.map (AlgHom.id F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) σ (1 ⊗ₜ[F] (a : E)) = -(1 ⊗ₜ[F] (a : E))
    rw [Algebra.TensorProduct.map_tmul, ha, map_one, TensorProduct.tmul_neg]
