core_files = files(
  'lapi.c',
  'lcode.c',
  'lctype.c',
  'ldebug.c',
  'ldo.c',
  'ldump.c',
  'lfunc.c',
  'lgc.c',
  'llex.c',
  'lmem.c',
  'lobject.c',
  'lopcodes.c',
  'lparser.c',
  'lstate.c',
  'lstring.c',
  'ltable.c',
  'ltm.c',
  'lundump.c',
  'lvm.c',
  'lzio.c',
)
aux_files  = files('lauxlib.c')
lib_files  = files(
  'lbaselib.c',
  'lcorolib.c',
  'ldblib.c',
  'linit.c',
  'liolib.c',
  'lmathlib.c',
  'loadlib.c',
  'loslib.c',
  'lstrlib.c',
  'ltablib.c',
  'lutf8lib.c',
)
hdr_files  = files('lua.h', 'luaconf.h', 'lualib.h', 'lauxlib.h', 'lua.hpp')
lua_files  = files('lua.c')
luac_files = files('luac.c')
inc_dirs   = include_directories('.')

if get_option('install_headers').enabled()
  install_headers(hdr_files, install_mode: 'rw-r--r--')
endif
