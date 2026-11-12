"""Bounded negative controls for the exact comparator Challenge-hole exception."""
import copy,hashlib,json,sys,unittest
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'scripts'))
from check_release import ROOT,check_challenge_config,check_challenge_text,check_proof_tokens,load_challenges
BASE='module\nnamespace Test\ntheorem result : True := by\n  sorry\nend Test\n'
class ChallengeHoles(unittest.TestCase):
 def test_compared_terminal_hole(self):check_proof_tokens('Challenge.lean',BASE,['Test.result'])
 def test_production_hole_rejected(self):
  with self.assertRaises(ValueError):check_proof_tokens('DirectedDistances/Example.lean',BASE)
 def test_solution_hole_rejected(self):
  with self.assertRaises(ValueError):check_proof_tokens('Palomar/Pilot/Solution.lean',BASE)
 def test_extra_tactic_before_hole_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE.replace('  sorry','  skip\n  sorry'),['Test.result'])
 def test_extra_tactic_after_hole_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE.replace('  sorry','  sorry\n  trivial'),['Test.result'])
 def test_noncompared_declaration_hole_rejected(self):
  text=BASE.replace('end Test','theorem extra : True := by sorry\nend Test')
  with self.assertRaises(ValueError):check_challenge_text(text,['Test.result'])
 def test_renamed_declaration_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE.replace('result :','different :'),['Test.result'])
 def test_nested_comment_is_masked(self):
  check_challenge_text(BASE.replace('  sorry','  /- sorry /- admit -/ -/ sorry'),['Test.result'])
 def test_admit_is_never_allowed(self):
  with self.assertRaises(ValueError):check_proof_tokens('Challenge.lean',BASE.replace('sorry','admit'),['Test.result'])
 def test_custom_axiom_is_never_allowed(self):
  with self.assertRaises(ValueError):check_proof_tokens('Challenge.lean',BASE+'axiom bad : False\n',['Test.result'])
 def test_hole_in_noncompared_definition_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE+'def extra : True := by sorry\n',['Test.result'])
 def test_actual_exact_challenges_and_configurations(self):
  self.assertEqual(sum(len(s['declarations']) for s in load_challenges().values()),7)
 def test_config_name_mismatch_rejected(self):
  spec=next(iter(load_challenges().values()));config=json.loads((ROOT/spec['config']).read_text())
  config['theorem_names']=['Test.other']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_config_extra_kernel_key_rejected(self):
  spec=next(iter(load_challenges().values()));config=json.loads((ROOT/spec['config']).read_text())
  config['external_kernels']=[]
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_config_nanoda_required(self):
  spec=next(iter(load_challenges().values()));config=json.loads((ROOT/spec['config']).read_text())
  config['enable_nanoda']=False
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
if __name__=='__main__':unittest.main()
