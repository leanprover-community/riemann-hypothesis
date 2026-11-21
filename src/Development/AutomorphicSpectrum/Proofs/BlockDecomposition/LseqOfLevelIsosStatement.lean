import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfLevelIsos
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk
import BuildAid.ForwardExisting

open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lseq_of_level_isos : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' T T' : Sys.{1} W) (e : Sys.Hom S T (RingHom.id W)) (e' : Sys.Hom S' T' (RingHom.id W)), (∀ n, Function.Bijective (e.f n)) → (∀ n, Function.Bijective (e'.f n)) → LSeq l S S' → Nonempty (LSeq l T T') := by
  atlas_forward_decl GlobalTheory.CompanionTheory.TowerSeq.lseq_transport
