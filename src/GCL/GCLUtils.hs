module GCL.GCLUtils(
   parseGCLstring,    -- parser, reading from string
   parseGCLfile,      -- parser, reading from a file
   ppProgram2String,  -- pretty printer
   echoTestParser,
   execProgram,       -- an interpreter to execute a GCL program
   mutateProgram      -- for injecting artificial errors in a program
)
where
import GCL.GCLParser.Parser
import GCL.GCLParser.PrettyPrint
import GCL.GCLInterpreter
import GCL.MuGCL

echoTestParser :: String -> IO()
echoTestParser filename = do
   gcl <- parseGCLfile filename
   let (Right prg) = gcl
   putStrLn . ppProgram2String $ prg
