import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.FiltrationSpanDividedPowers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelOneFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelSequenceFacts

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem CrystallineSemistableComparison.RL.d_ob : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.ObFacts l := GlobalTheory.T.integral_ring_facts

theorem CrystallineSemistableComparison.RL.acris_mod_l_base_change : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcr1 l := GlobalTheory.T.acris_level_one_facts

theorem CrystallineSemistableComparison.RL.d_seq : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcrSeq l := GlobalTheory.T.acris_level_sequence_facts
end

section
set_option backward.isDefEq.respectTransparency false

open CrystallineSemistableComparison.PAlg

theorem CrystallineSemistableComparison.R.forD (l : ℕ) [Fact l.Prime] : CrystallineSemistableComparison.D.RIn l :=
  ⟨RL.d_ob l, RL.acris_mod_l_base_change l, RL.d_seq l, fun A => ⟨(RL.u_tf A).1, fun x => by
    rw [← (RL.u_mod A).2, RingHom.mem_ker, sharpMap_coeff, Ideal.Quotient.eq_zero_iff_mem, pow_one]⟩, fun A n r => RL.gr A n r⟩
end
