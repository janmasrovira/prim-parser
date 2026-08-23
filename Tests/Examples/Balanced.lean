import Examples.Balanced
import Tests.Basic

open Parser Parser.Utf8 Balanced

#guard group.runOption "()" == some ()
#guard group.runOption "(())" == some ()
#guard group.runOption "(()())" == some ()
#guard group.runOption "((()))" == some ()

#guard group.runOption "" == none
#guard group.runOption "(" == none
#guard group.runOption "(()" == none
#guard group.runOption ")(" == none

#guard balanced.runOption "" == some ()
#guard balanced.runOption "()" == some ()
#guard balanced.runOption "()()" == some ()
#guard balanced.runOption "(())()" == some ()
