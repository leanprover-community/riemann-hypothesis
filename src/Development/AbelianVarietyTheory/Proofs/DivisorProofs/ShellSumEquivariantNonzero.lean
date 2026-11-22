module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralShellsVanishBeyondPeriodRamifiedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanAntitone
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableZetaIntegrand
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section
namespace GlobalTheory.ShellSumEqv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unique_shell {ϖ : kˣ} (hϖ : IsUnif ϖ) {a : ℕ} (g : GL (Fin a) k) :
    ∃! m : {m : Fin a → ℤ // Antitone m}, g ∈ shellSet ϖ m.1 := by
  obtain ⟨m, hm, x, hx, y, hy, e⟩ := GlobalTheory.SortedCartan.cartan_antitone k a ϖ hϖ g
  have ht : ∀ m : Fin a → ℤ, GlobalTheory.GLDoubling.torusElt k (Fin a) ϖ m = diagGL fun i => ϖ ^ m i :=
    fun m => Units.ext (by rw [GlobalTheory.GLDoubling.val_torusElt, diagGL_val]; simp [Units.val_zpow_eq_zpow_val])
  refine ⟨⟨m, hm⟩, mem_shellSet.2 ⟨x, hx, y, hy, by rw [e, ht]⟩, ?_⟩
  rintro ⟨m', hm'⟩ hmem
  obtain ⟨x', hx', y', hy', e'⟩ := mem_shellSet.1 hmem
  have E : (x'⁻¹ * x) * diagGL (fun i => ϖ ^ m i) * (y * y'⁻¹) = diagGL fun i => ϖ ^ m' i := by
    have h1 : x * diagGL (fun i => ϖ ^ m i) * y = x' * diagGL (fun i => ϖ ^ m' i) * y' := by
      rw [← ht, ← e]; exact e'
    calc _ = x'⁻¹ * (x * diagGL (fun i => ϖ ^ m i) * y) * y'⁻¹ := by group
      _ = _ := by rw [h1]; group
  have E' := congrArg Units.val E
  simp only [Units.val_mul, diagGL_val, Units.val_zpow_eq_zpow_val] at E'
  exact Subtype.ext (Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
    (hϖ ▸ uniformizer_lt_one) m m' hm hm' (x'⁻¹ * x) (mul_mem (inv_mem hx') hx) (y * y'⁻¹)
    (mul_mem hy (inv_mem hy')) (by simpa only [Units.val_mul] using E')).symm

theorem isOpen_shellSet (ϖ : kˣ) {a : ℕ} (m : Fin a → ℤ) : IsOpen (shellSet ϖ m : Set (GL (Fin a) k)) := by
  have : shellSet ϖ m = ⋃ x ∈ (KO k (Fin a) : Set (GL (Fin a) k)),
      (fun g => (x * diagGL (fun i => ϖ ^ m i))⁻¹ * g) ⁻¹' (KO k (Fin a) : Set _) := by
    ext g
    simp only [mem_shellSet, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, hx, by simpa [mul_assoc] using hy⟩
    · rintro ⟨x, hx, hy⟩
      exact ⟨x, hx, _, hy, by group⟩
  rw [this]
  exact isOpen_biUnion fun x _ => isOpen_KO.preimage (continuous_const.mul continuous_id)

variable [MeasurableSpace k] [BorelSpace k]

section Shells
variable {ϖ : kˣ} {ν : kˣ →* ℂˣ} {e : ℕ}

end Shells

section Main
variable {ϖ : kˣ} {ν : kˣ →* ℂˣ} {e : ℕ}

end Main

end GlobalTheory.ShellSumEqv
