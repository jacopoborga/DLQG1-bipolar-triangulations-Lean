"""Regression tests for the release checker's Lean lexical masking."""
import sys,unittest
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'scripts'))
from lean_syntax import pieces,command_tokens
class LexicalMasking(unittest.TestCase):
 def test_nested_comments(self):self.assertEqual(command_tokens('module /- x /- sorry -/ -/\ndef a := 1'),command_tokens('module\ndef a := 1'))
 def test_quoted_identifier_does_not_start_line_comment(self):self.assertIn(('code','sorry'),command_tokens('module\ndef «safe--x» := by sorry'))
 def test_string_does_not_start_comment(self):self.assertIn(('literal','"/- sorry -/"'),command_tokens('module\ndef a := "/- sorry -/"'))
 def test_unclosed_string_rejected(self):
  with self.assertRaises(ValueError):list(pieces('module\ndef a := "unfinished'))
 def test_unclosed_identifier_rejected(self):
  with self.assertRaises(ValueError):list(pieces('module\ndef «unfinished'))
 def test_escaped_quote_character(self):self.assertTrue(command_tokens("module\ndef a : Char := '\\\"'"))
if __name__=='__main__':unittest.main()
