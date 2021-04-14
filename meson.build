#
# Lua Project Declaration
#
project('Lua', 'c',
  license: 'MIT',
  version: '5.4.3',
  meson_version: '>=0.57.2',
  default_options: [
    'c_std=gnu99',
    'warning_level=2',
    'optimization=2',
    'debug=false',
    'buildtype=custom',
    'b_ndebug=false',
    'b_asneeded=false',
    'strip=true',
  ],
)


#
# Module imports
#
fs        = import('fs')
pkgconfig = import('pkgconfig')


#
# Version check
#
# `make pc` prints, as the first line, version=$R where $R is the release
# version. We assert that this quantity is equal to the project version
# recorded above.
#
# If `make` cannot be found or runs unsuccessfully, silently ignore this
# sanity check.
#
if fs.is_file('Makefile')
  Makefile = files('Makefile')
  make = find_program('make', required: false)
  if make.found()
    version = run_command(make, ['-f', Makefile, 'pc'])
    if version.returncode() == 0
      version = version.stdout().split('\n')[0].strip()
      if version.startswith('version=')
        version = version.split('=')[-1].strip()
        assert(version == meson.project_version())
      endif
    endif
  endif
endif


#
# System check
#
HOST_SYSTEM       = host_machine.system()
IS_HOST_LINUX     = HOST_SYSTEM == 'linux'
IS_HOST_DARWIN    = HOST_SYSTEM == 'darwin'
#IS_HOST_WINDOWS   = HOST_SYSTEM == 'windows'
IS_HOST_SUNOS     = HOST_SYSTEM == 'sunos'
IS_HOST_PLAIN_BSD = HOST_SYSTEM in ['freebsd', 'netbsd', 'openbsd']
IS_HOST_BSD       = HOST_SYSTEM in ['dragonfly'] or HOST_SYSTEM.contains('bsd')
IS_HOST_POSIX     = HOST_SYSTEM not in ['windows', 'emscripten', 'android']


#
# Compiler, Dependencies & Libraries
#
cc          = meson.get_compiler('c')
threads     = dependency('threads')
libm        = cc.find_library('m',        required: false)
libdl       = cc.find_library('dl',       required: false)
libreadline = cc.find_library('readline', required: get_option('lineedit')=='readline')
libedit     = cc.find_library('edit',     required: get_option('lineedit')=='edit')


#
# Source code, headers, manuals
#
subdir('doc')
subdir('src')


#
# Compiler and Linker Flags, Part I
#
c_args = []
c_args += IS_HOST_POSIX             ? ['-DLUA_USE_POSIX']  : []
c_args += IS_HOST_SUNOS             ? ['-D_REENTRANT']     : []
c_args += get_option('lua53compat') ? ['-DLUA_COMPAT_5_3'] : []
if get_option('c_std') in ['c89', 'gnu89']
  warning('\n*** C89 does not guarantee 64-bit integers for Lua.\n'+
            '*** Make sure to compile all external Lua libraries\n'+
            '*** with LUA_USE_C89 to ensure consistency')
  c_args += ['-DLUA_USE_C89']
endif
deps = declare_dependency(dependencies: [libm], compile_args: c_args)


#
# Build the Lua compiler
#
if cc.get_argument_syntax() == 'gcc'
  luac_c_args = cc.get_supported_arguments(['-ffunction-sections', '-fno-PIC'])
else
  luac_c_args = []
endif
luac = executable('luac', core_files+aux_files+luac_files,
  c_args:       luac_c_args,
  dependencies: deps,
  install_mode: 'rwxr-xr-x',
  install:      get_option('install_luac').enabled(),
  implicit_include_directories: false,
  pie:          false,
  override_options: [
    'optimization=s',
    'debug=false',
    'buildtype=minsize',
    'b_ndebug=true',
    'b_asneeded=true',
    'b_pie=false',
    'strip=true',
  ]
)


#
# Compiler and Linker Flags, Part II
#
if   get_option('lineedit') == 'none'
elif get_option('lineedit') == 'readline'
  deps = declare_dependency(dependencies: [deps, libreadline],
                            compile_args: ['-DLUA_USE_READLINE'])
elif get_option('lineedit') == 'edit'
  if IS_HOST_PLAIN_BSD and fs.is_dir('/usr/include/edit')
    deps = declare_dependency(dependencies: [deps, libedit],
                              compile_args: ['-DLUA_USE_READLINE'],
                              include_directories: ['/usr/include/edit'])
  else
    deps = declare_dependency(dependencies: [deps, libedit],
                              compile_args: ['-DLUA_USE_READLINE'])
  endif
else
  error('Unknown line-editing library \''+get_option('lineedit')+'\'!')
endif

if libdl.found()
  deps = declare_dependency(dependencies: [deps, libdl],
                            compile_args: ['-DLUA_USE_DLOPEN'])
endif

# Platform 'macosx'  doesn't need -ldl
# Platform 'linux'   does (with glibc), but maybe does not elsewhere (e.g. with musl)
# Platform 'freebsd' doesn't need -ldl (?) according to Makefile because bsd-libc
#                    includes it.

if get_option('threads')
  deps = declare_dependency(dependencies: [deps, threads])
endif

#
# Build the Lua interpreter
#
lua = executable('lua',  core_files+aux_files+lib_files+lua_files,
  dependencies:   [deps],
  install_mode:   'rwxr-xr-x',
  install:        get_option('install_lua').enabled(),
  export_dynamic: IS_HOST_LINUX or IS_HOST_BSD,
  implicit_include_directories: false,
)


#
# Generate the pkg-config file
#
#if get_option('install_pkgconfig').enabled()
#  pkgconfig.generate(liblua, version: meson.project_version())
#endif
