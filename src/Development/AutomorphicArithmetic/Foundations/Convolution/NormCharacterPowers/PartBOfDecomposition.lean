import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.BcSumD
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.GaloisGenerators.LocRoots
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep PositivityTheory.RgJS PositivityTheory.Rg.Tf.ChR

namespace UpperTheory.ConvolutionTheory.R

namespace Pb2

theorem val_pow {E : Type} [Field E] [NumberField E] (η : HChar E) (j : ℕ) (v : HeightOneSpectrum (𝓞 E)) :
    (η ^ j).val v = η.val v ^ j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, pow_succ, ← ih]; rfl

theorem bd {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} {π : CG E n} (hπ : π.IsUnitary)
    {S : Finset (HeightOneSpectrum (𝓞 E))} {α : Off E S → Fin n → ℂˣ} (hα : SatOff π S α) (v : Off E S) (a : Fin n) :
    ‖(α v a : ℂ)‖ ≤ Real.sqrt (nq v) := by
  rw [Real.sqrt_eq_rpow]
  exact (PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound E n π hπ v.1 _ (hα v) (α v a) (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))).2.le

theorem fam {n f q q' : ℕ} {A α : Fin n → ℂˣ} (h : Finset.univ.val.map A = Finset.univ.val.map fun a => α a ^ f)
    (hq : q' = q ^ f) (hα : ∀ a, ‖(α a : ℂ)‖ ≤ Real.sqrt q) :
    (∀ k : ℕ, ∑ a, (A a : ℂ) ^ k = ∑ a, (α a : ℂ) ^ (f * k)) ∧ ∀ a, ‖(A a : ℂ)‖ ≤ Real.sqrt q' := by
  refine ⟨fun k => ?_, fun a => ?_⟩
  · have := congrArg (fun m : Multiset ℂˣ => (m.map fun z : ℂˣ => (z : ℂ) ^ k).sum) h
    simp only [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum, Units.val_pow_eq_pow_val, ← pow_mul] at this
    exact this
  · have hm : A a ∈ Finset.univ.val.map fun a => α a ^ f := h ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val a)
    obtain ⟨b, -, e⟩ := Multiset.mem_map.1 hm
    rw [← e, hq, Units.val_pow_eq_pow_val, norm_pow, Nat.cast_pow]
    refine (pow_le_pow_left₀ (norm_nonneg _) (hα b) f).trans (Real.le_sqrt_of_sq_le (le_of_eq ?_))
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]

end Pb2

open Pb2


end UpperTheory.ConvolutionTheory.R
