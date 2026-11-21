import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.SecondWayHolds
import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.BaseCaseFalseGeneralHolds
import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.FixAll

namespace Formalism.BaseCaseIdentities.Final

open Formalism.BaseCaseIdentities

alias frobenius_spectrum := frobeniusSubstSpec
alias psi_is_limit := Data.opIsLimit
alias chainI := Data.chainI_holds
alias contractionAlt := Data.contracts
alias fixed_point_alt := Data.hasUniqueFixedPoint
alias start_in_W := Data.start_in_W_holds
alias psi_in_W := Data.psi_in_W_holds
alias chainII := Data.chainII_holds
alias second_way := Data.second_way_holds
alias base_case_k_one := Data.base_case_k_one_holds

alias mul_rule := weighted_mul_rule
alias pow_rule := weighted_pow_rule
alias mul_rule_two := mul_rule_two_holds
alias pow_rule_two := pow_rule_two_holds
alias coeff_minus_one := Data.coeff_minus_one_holds
alias base_case_false_general := Data.base_case_false_general_holds
alias q_sigma_small := Data.QSigmaSmall_statement

alias unit_entries_alt := Data.unit_entry_all
alias start_eq_zero := Data.start_eq_z
alias log_iff_fixed_point := Data.LogIffFix_statement
alias log_unique_alt := Data.log_unique_bis
alias chainII_log := Data.chain_ii_of_log

end Formalism.BaseCaseIdentities.Final
