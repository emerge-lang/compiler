# Config for building the installer
!ifndef VERSION
!error "Set the version when running the makensis compiler: /DVERSION=1.4.3"
!endif
!ifndef JRE_DIR
!error "Set JRE_DIR to the location of the JRE to bundle with the installer, /DJRE_DIR=..."
!endif

# configuration for how to install
InstallDir "$PROGRAMFILES64\emerge-toolchain\${VERSION}"
!define /ifndef RegkeyHKLM "Software\EmergeToolchain\${VERSION}"

# configuration for how the installer looks
SetCompressor lzma
ShowInstDetails show

Page directory
Page instfiles

UninstPage uninstConfirm
UninstPage instfiles

# Installation Logic

Function .onInit
SetRegView 64
ClearErrors
ReadRegStr $0 HKLM ${RegkeyHKLM} "InstallationDirectory"
IfErrors 0 +2
    Return
StrCpy $0 "It seems version ${VERSION} of the toolchain is already installed at $0.$\n$\nClean up HKLM\${RegkeyHKLM} to fix this."
IfSilent +2 0
    MessageBox MB_OK $0
Abort $0
FunctionEnd


Section #unpack
DetailPrint "Unpacking toolchain files"
SetOutPath $INSTDIR\bin
File /oname=toolchain.jar ..\..\toolchain\target\toolchain.jar
SetOutPath $INSTDIR
File /r "${JRE_DIR}"
SectionEnd

Section #register-installation
DetailPrint "Registering this installation in HKLM\${RegkeyHKLM}"
#WriteRegStr HKLM ${RegkeyHKLM} "InstallationDirectory" "$INSTDIR"
SectionEnd

Section "Uninstall"
DeleteRegKey HKLM ${RegkeyHKLM}
RMDir /r $INSTDIR
SectionEnd