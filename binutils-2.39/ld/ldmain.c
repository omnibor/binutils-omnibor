/* Main program of GNU linker.
   Copyright (C) 1991-2022 Free Software Foundation, Inc.
   Written by Steve Chamberlain steve@cygnus.com

   This file is part of the GNU Binutils.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street - Fifth Floor, Boston,
   MA 02110-1301, USA.  */

#include "sysdep.h"
#include "bfd.h"
#include "safe-ctype.h"
#include "libiberty.h"
#include "progress.h"
#include "bfdlink.h"
#include "ctf-api.h"
#include "filenames.h"
#include "elf/common.h"

#include "ld.h"
#include "ldmain.h"
#include "ldmisc.h"
#include "ldwrite.h"
#include "ldexp.h"
#include "ldlang.h"
#include <ldgram.h>
#include "ldlex.h"
#include "ldfile.h"
#include "ldemul.h"
#include "ldctor.h"
#include "ldelf.h"
#if BFD_SUPPORTS_PLUGINS
#include "plugin.h"
#include "plugin-api.h"
#endif /* BFD_SUPPORTS_PLUGINS */

#include "sha1.h"
#include "sha256.h"
#include <dirent.h>

#define GITOID_LENGTH_SHA1 20
#define GITOID_LENGTH_SHA256 32
#define MAX_FILE_SIZE_STRING_LENGTH 256

/* Somewhere above, sys/stat.h got included.  */
#if !defined(S_ISDIR) && defined(S_IFDIR)
#define	S_ISDIR(m) (((m) & S_IFMT) == S_IFDIR)
#endif

#include <string.h>

#ifndef TARGET_SYSTEM_ROOT
#define TARGET_SYSTEM_ROOT ""
#endif

static char *omnibor_dir;

/* EXPORTS */

FILE *saved_script_handle = NULL;
FILE *previous_script_handle = NULL;
bool force_make_executable = false;

char *default_target;
const char *output_filename = "a.out";

/* Name this program was invoked by.  */
char *program_name;

/* The prefix for system library directories.  */
const char *ld_sysroot;

/* The canonical representation of ld_sysroot.  */
char *ld_canon_sysroot;
int ld_canon_sysroot_len;

/* Set by -G argument, for targets like MIPS ELF.  */
int g_switch_value = 8;

/* Nonzero means print names of input files as processed.  */
unsigned int trace_files;

/* Nonzero means report actions taken by the linker, and describe the linker script in use.  */
bool verbose;

/* Nonzero means version number was printed, so exit successfully
   instead of complaining if no input files are given.  */
bool version_printed;

/* TRUE if we should demangle symbol names.  */
bool demangling;

args_type command_line;

ld_config_type config;

sort_type sort_section;

static const char *get_sysroot
  (int, char **);
static char *get_emulation
  (int, char **);
static bool add_archive_element
  (struct bfd_link_info *, bfd *, const char *, bfd **);
static void multiple_definition
  (struct bfd_link_info *, struct bfd_link_hash_entry *,
   bfd *, asection *, bfd_vma);
static void multiple_common
  (struct bfd_link_info *, struct bfd_link_hash_entry *,
   bfd *, enum bfd_link_hash_type, bfd_vma);
static void add_to_set
  (struct bfd_link_info *, struct bfd_link_hash_entry *,
   bfd_reloc_code_real_type, bfd *, asection *, bfd_vma);
static void constructor_callback
  (struct bfd_link_info *, bool, const char *, bfd *,
   asection *, bfd_vma);
static void warning_callback
  (struct bfd_link_info *, const char *, const char *, bfd *,
   asection *, bfd_vma);
static void warning_find_reloc
  (bfd *, asection *, void *);
static void undefined_symbol
  (struct bfd_link_info *, const char *, bfd *, asection *, bfd_vma,
   bool);
static void reloc_overflow
  (struct bfd_link_info *, struct bfd_link_hash_entry *, const char *,
   const char *, bfd_vma, bfd *, asection *, bfd_vma);
static void reloc_dangerous
  (struct bfd_link_info *, const char *, bfd *, asection *, bfd_vma);
static void unattached_reloc
  (struct bfd_link_info *, const char *, bfd *, asection *, bfd_vma);
static bool notice
  (struct bfd_link_info *, struct bfd_link_hash_entry *,
   struct bfd_link_hash_entry *, bfd *, asection *, bfd_vma, flagword);

static struct bfd_link_callbacks link_callbacks =
{
  add_archive_element,
  multiple_definition,
  multiple_common,
  add_to_set,
  constructor_callback,
  warning_callback,
  undefined_symbol,
  reloc_overflow,
  reloc_dangerous,
  unattached_reloc,
  notice,
  einfo,
  info_msg,
  minfo,
  ldlang_override_segment_assignment,
  ldlang_ctf_acquire_strings,
  NULL,
  ldlang_ctf_new_dynsym,
  ldlang_write_ctf_late
};

static bfd_assert_handler_type default_bfd_assert_handler;
static bfd_error_handler_type default_bfd_error_handler;

struct bfd_link_info link_info;

struct dependency_file
{
  struct dependency_file *next;
  char *name;
};

static struct dependency_file *dependency_files, *dependency_files_tail;

void
track_dependency_files (const char *filename)
{
  struct dependency_file *dep
    = (struct dependency_file *) xmalloc (sizeof (*dep));
  dep->name = xstrdup (filename);
  dep->next = NULL;
  if (dependency_files == NULL)
    dependency_files = dep;
  else
    dependency_files_tail->next = dep;
  dependency_files_tail = dep;
}

static void
write_dependency_file (void)
{
  FILE *out;
  struct dependency_file *dep;

  out = fopen (config.dependency_file, FOPEN_WT);
  if (out == NULL)
    {
      einfo (_("%F%P: cannot open dependency file %s: %E\n"),
	     config.dependency_file);
    }

  fprintf (out, "%s:", output_filename);

  for (dep = dependency_files; dep != NULL; dep = dep->next)
    fprintf (out, " \\\n  %s", dep->name);

  fprintf (out, "\n");
  for (dep = dependency_files; dep != NULL; dep = dep->next)
    fprintf (out, "\n%s:\n", dep->name);

  fclose (out);
}

/* OmniBOR struct which contains the names of the directories from the path
   to the directory where the OmniBOR information is to be stored.  */

struct omnibor_dirs
{
  struct omnibor_dirs *next;
  DIR *dir;
};

static struct omnibor_dirs *omnibor_dirs_head, *omnibor_dirs_tail;

static void
omnibor_add_to_dirs (DIR **directory)
{
  struct omnibor_dirs *elem
    = (struct omnibor_dirs *) xmalloc (sizeof (*elem));
  elem->dir = *directory;
  elem->next = NULL;
  if (omnibor_dirs_head == NULL)
    omnibor_dirs_head = elem;
  else
    omnibor_dirs_tail->next = elem;
  omnibor_dirs_tail = elem;
}

/* Return the position of the first occurrence after start_pos position
   of char c in str string (start_pos is the first position to check).  */

static int
omnibor_find_char_from_pos (unsigned start_pos, char c, const char *str)
{
  for (unsigned ix = start_pos; ix < strlen (str); ix++)
    if (str[ix] == c)
      return ix;

  return -1;
}

/* Append the string str2 to the end of the string str1.  */

static void
omnibor_append_to_string (char **str1, const char *str2,
			 unsigned long len1, unsigned long len2)
{
  *str1 = (char *) xrealloc
	(*str1, sizeof (char) * (len1 + len2 + 1));
  memcpy (*str1 + len1, str2, len2);
  (*str1)[len1 + len2] = '\0';
}

/* Add the string str2 as a prefix to the string str1.  */

static void
omnibor_add_prefix_to_string (char **str1, const char *str2)
{
  unsigned len1 = strlen (*str1), len2 = strlen (str2);
  char *temp = (char *) xcalloc
	(len1 + len2 + 1, sizeof (char));
  memcpy (temp, str2, len2);
  memcpy (temp + len2, *str1, len1);
  temp[len1 + len2] = '\0';
  *str1 = (char *) xrealloc
	(*str1, sizeof (char) * (len1 + len2 + 1));
  memcpy (*str1, temp, len1 + len2);
  (*str1)[len1 + len2] = '\0';
  free (temp);
}

/* Get the substring of length len of the str2 string starting from
   the start position and put it in the str1 string.  */

static void
omnibor_substr (char **str1, unsigned start, unsigned len, const char *str2)
{
  *str1 = (char *) xrealloc
	(*str1, sizeof (char) * (len + 1));
  memcpy (*str1, str2 + start, len);
  (*str1)[len] = '\0';
}

/* Set the string str1 to have the contents of the string str2.  */

static void
omnibor_set_contents (char **str1, const char *str2, unsigned long len)
{
  *str1 = (char *) xrealloc
	(*str1, sizeof (char) * (len + 1));
  memcpy (*str1, str2, len);
  (*str1)[len] = '\0';
}

/* Open all the directories from the path specified in the res_dir
   parameter and put them in the omnibor_dirs_head list.  Also create
   the directories which do not already exist.  */

static DIR *
open_all_directories_in_path (const char *res_dir)
{
  char *path = (char *) xcalloc (1, sizeof (char));
  char *dir_name = (char *) xcalloc (1, sizeof (char));

  int old_p = 0, p = omnibor_find_char_from_pos (0, '/', res_dir);
  int dfd, absolute = 0;
  DIR *dir = NULL;

  if (p == -1)
    {
      free (dir_name);
      free (path);
      return NULL;
    }
  /* If the res_dir is an absolute path.  */
  else if (p == 0)
    {
      absolute = 1;
      omnibor_append_to_string (&path, "/", strlen (path), strlen ("/"));
      /* Opening a root directory because an absolute path is specified.  */
      dir = opendir (path);
      dfd = dirfd (dir);

      omnibor_add_to_dirs (&dir);
      p = p + 1;
      old_p = p;

      /* Path is of format "/<dir>" where dir does not exist.  This point can be
         reached only if <dir> could not be created in the root folder, so it is
         considered as an illegal path.  */
      if ((p = omnibor_find_char_from_pos (p, '/', res_dir)) == -1)
        {
	  free (dir_name);
	  free (path);
	  return NULL;
	}

      /* Process sequences of adjacent occurrences of character '/'.  */
      while (old_p == p)
        {
          p = p + 1;
          old_p = p;
          p = omnibor_find_char_from_pos (p, '/', res_dir);
        }

      if (p == -1)
        {
	  free (dir_name);
	  free (path);
	  return NULL;
	}
    }

  omnibor_substr (&dir_name, old_p, p - old_p, res_dir);
  omnibor_append_to_string (&path, dir_name, strlen (path), strlen (dir_name));

  if ((dir = opendir (path)) == NULL)
    {
      if (absolute)
        mkdirat (dfd, dir_name, S_IRWXU);
      else
        mkdir (dir_name, S_IRWXU);
      dir = opendir (path);
    }

  if (dir == NULL)
    {
      free (dir_name);
      free (path);
      return NULL;
    }

  dfd = dirfd (dir);

  omnibor_add_to_dirs (&dir);
  p = p + 1;
  old_p = p;

  while ((p = omnibor_find_char_from_pos (p, '/', res_dir)) != -1)
    {
      /* Process sequences of adjacent occurrences of character '/'.  */
      while (old_p == p)
        {
          p = p + 1;
          old_p = p;
          p = omnibor_find_char_from_pos (p, '/', res_dir);
        }

      if (p == -1)
        break;

      omnibor_substr (&dir_name, old_p, p - old_p, res_dir);
      omnibor_append_to_string (&path, "/", strlen (path), strlen ("/"));
      omnibor_append_to_string (&path, dir_name, strlen (path),
				strlen (dir_name));

      if ((dir = opendir (path)) == NULL)
        {
          mkdirat (dfd, dir_name, S_IRWXU);
          dir = opendir (path);
        }

      if (dir == NULL)
        {
	  free (dir_name);
	  free (path);
	  return NULL;
	}

      dfd = dirfd (dir);

      omnibor_add_to_dirs (&dir);
      p = p + 1;
      old_p = p;
    }

  if ((unsigned) old_p < strlen (res_dir))
    {
      omnibor_substr (&dir_name, old_p, strlen (res_dir) - old_p, res_dir);
      omnibor_append_to_string (&path, "/", strlen (path), strlen ("/"));
      omnibor_append_to_string (&path, dir_name, strlen (path),
				strlen (dir_name));

      if ((dir = opendir (path)) == NULL)
        {
          mkdirat (dfd, dir_name, S_IRWXU);
          dir = opendir (path);
        }

      omnibor_add_to_dirs (&dir);
    }

  free (dir_name);
  free (path);
  return dir;
}

/* Close all the directories from the omnibor_dirs_head list.  This function
   should be called after calling the function open_all_directories_in_path.  */

static void
close_all_directories_in_path (void)
{
  struct omnibor_dirs *dir = omnibor_dirs_head, *old = NULL;
  while (dir != NULL)
    {
      closedir (dir->dir);
      old = dir;
      dir = dir->next;
      free (old);
    }

  omnibor_dirs_head = NULL;
  omnibor_dirs_tail = NULL;
}

/* Calculate the SHA1 gitoid using the contents of the given file.  */

static void
calculate_sha1_omnibor (FILE *dep_file, unsigned char resblock[])
{
  fseek (dep_file, 0L, SEEK_END);
  long file_size = ftell (dep_file);
  fseek (dep_file, 0L, SEEK_SET);

  /* This length should be enough for everything up to 64B, which should
     cover long type.  */
  char buff_for_file_size[MAX_FILE_SIZE_STRING_LENGTH];
  sprintf (buff_for_file_size, "%ld", file_size);

  char *init_data = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&init_data, "blob ", strlen (init_data),
			    strlen ("blob "));
  omnibor_append_to_string (&init_data, buff_for_file_size, strlen (init_data),
			    strlen (buff_for_file_size));
  omnibor_append_to_string (&init_data, "\0", strlen (init_data), 1);

  char *file_contents = (char *) xcalloc (file_size, sizeof (char));
  fread (file_contents, 1, file_size, dep_file);

  /* Calculate the hash.  */
  struct sha1_ctx ctx;

  sha1_init_ctx (&ctx);

  sha1_process_bytes (init_data, strlen (init_data) + 1, &ctx);
  sha1_process_bytes (file_contents, file_size, &ctx);

  sha1_finish_ctx (&ctx, resblock);

  free (file_contents);
  free (init_data);
}

/* Calculate the SHA1 gitoid using the given contents.  */

static void
calculate_sha1_omnibor_with_contents (char *contents,
				      unsigned char resblock[])
{
  long file_size = strlen (contents);

  /* This length should be enough for everything up to 64B, which should
     cover long type.  */
  char buff_for_file_size[MAX_FILE_SIZE_STRING_LENGTH];
  sprintf (buff_for_file_size, "%ld", file_size);

  char *init_data = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&init_data, "blob ", strlen (init_data),
			    strlen ("blob "));
  omnibor_append_to_string (&init_data, buff_for_file_size, strlen (init_data),
			    strlen (buff_for_file_size));
  omnibor_append_to_string (&init_data, "\0", strlen (init_data), 1);

  /* Calculate the hash.  */
  struct sha1_ctx ctx;

  sha1_init_ctx (&ctx);

  sha1_process_bytes (init_data, strlen (init_data) + 1, &ctx);
  sha1_process_bytes (contents, file_size, &ctx);

  sha1_finish_ctx (&ctx, resblock);

  free (init_data);
}

/* Calculate the SHA256 gitoid using the contents of the given file.  */

static void
calculate_sha256_omnibor (FILE *dep_file, unsigned char resblock[])
{
  fseek (dep_file, 0L, SEEK_END);
  long file_size = ftell (dep_file);
  fseek (dep_file, 0L, SEEK_SET);

  /* This length should be enough for everything up to 64B, which should
     cover long type.  */
  char buff_for_file_size[MAX_FILE_SIZE_STRING_LENGTH];
  sprintf (buff_for_file_size, "%ld", file_size);

  char *init_data = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&init_data, "blob ", strlen (init_data),
			    strlen ("blob "));
  omnibor_append_to_string (&init_data, buff_for_file_size, strlen (init_data),
			    strlen (buff_for_file_size));
  omnibor_append_to_string (&init_data, "\0", strlen (init_data), 1);

  char *file_contents = (char *) xcalloc (file_size, sizeof (char));
  fread (file_contents, 1, file_size, dep_file);

  /* Calculate the hash.  */
  struct sha256_ctx ctx;

  sha256_init_ctx (&ctx);

  sha256_process_bytes (init_data, strlen (init_data) + 1, &ctx);
  sha256_process_bytes (file_contents, file_size, &ctx);

  sha256_finish_ctx (&ctx, resblock);

  free (file_contents);
  free (init_data);
}

/* Calculate the SHA256 gitoid using the given contents.  */

static void
calculate_sha256_omnibor_with_contents (char *contents,
					unsigned char resblock[])
{
  long file_size = strlen (contents);

  /* This length should be enough for everything up to 64B, which should
     cover long type.  */
  char buff_for_file_size[MAX_FILE_SIZE_STRING_LENGTH];
  sprintf (buff_for_file_size, "%ld", file_size);

  char *init_data = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&init_data, "blob ", strlen (init_data),
			    strlen ("blob "));
  omnibor_append_to_string (&init_data, buff_for_file_size, strlen (init_data),
			    strlen (buff_for_file_size));
  omnibor_append_to_string (&init_data, "\0", strlen (init_data), 1);

  /* Calculate the hash.  */
  struct sha256_ctx ctx;

  sha256_init_ctx (&ctx);

  sha256_process_bytes (init_data, strlen (init_data) + 1, &ctx);
  sha256_process_bytes (contents, file_size, &ctx);

  sha256_finish_ctx (&ctx, resblock);

  free (init_data);
}

/* OmniBOR dependency file struct which contains its SHA1 gitoid, its SHA256
   gitoid and its filename.  */

struct omnibor_deps
{
  struct omnibor_deps *next;
  char *sha1_contents;
  char *sha256_contents;
  char *name;
};

static struct omnibor_deps *omnibor_deps_head, *omnibor_deps_tail;

static void
omnibor_add_to_deps (char *filename, char *sha1_contents, char *sha256_contents,
		     unsigned long sha1_contents_len,
		     unsigned long sha256_contents_len)
{
  struct omnibor_deps *elem
    = (struct omnibor_deps *) xmalloc (sizeof (*elem));
  elem->name = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&elem->name, filename, strlen (elem->name),
			    strlen (filename));
  if (sha1_contents != NULL)
    {
      elem->sha1_contents = (char *) xcalloc (1, sizeof (char));
      omnibor_append_to_string (&elem->sha1_contents, sha1_contents,
				strlen (elem->sha1_contents),
				sha1_contents_len);
    }
  else
    elem->sha1_contents = NULL;
  if (sha256_contents != NULL)
    {
      elem->sha256_contents = (char *) xcalloc (1, sizeof (char));
      omnibor_append_to_string (&elem->sha256_contents, sha256_contents,
				strlen (elem->sha256_contents),
				sha256_contents_len);
    }
  else
    elem->sha256_contents = NULL;
  elem->next = NULL;
  if (omnibor_deps_head == NULL)
    omnibor_deps_head = elem;
  else
    omnibor_deps_tail->next = elem;
  omnibor_deps_tail = elem;
}

static void
omnibor_clear_deps (void)
{
  struct omnibor_deps *dep = omnibor_deps_head, *old = NULL;
  while (dep != NULL)
    {
      free (dep->name);
      if (dep->sha1_contents)
        free (dep->sha1_contents);
      if (dep->sha256_contents)
        free (dep->sha256_contents);
      old = dep;
      dep = dep->next;
      free (old);
    }

  omnibor_deps_head = NULL;
  omnibor_deps_tail = NULL;
}

static struct omnibor_deps *
omnibor_is_dep_present (const char *name)
{
  struct omnibor_deps *dep;
  for (dep = omnibor_deps_head; dep != NULL; dep = dep->next)
    if (strcmp (name, dep->name) == 0)
      return dep;

  return NULL;
}

/* Sort the contents of the OmniBOR Document file using the selection sort
   algorithm.  The parameter ind should be either 0 (sort the SHA1 OmniBOR
   Document file) or 1 (sort the SHA256 OmniBOR Document file).  */

static void
omnibor_sort (unsigned int ind)
{
  if (omnibor_deps_head == NULL || omnibor_deps_head->next == NULL
      || (ind != 0 && ind != 1))
    return;

  struct omnibor_deps *dep1, *dep2, *curr;
  for (dep1 = omnibor_deps_head; dep1 != NULL; dep1 = dep1->next)
    {
      curr = dep1;
      for (dep2 = dep1->next; dep2 != NULL; dep2 = dep2->next)
        {
          if ((dep1->sha1_contents == NULL && dep2->sha1_contents != NULL)
               || (dep1->sha1_contents != NULL && dep2->sha1_contents == NULL)
               || (dep1->sha256_contents == NULL && dep2->sha256_contents != NULL)
               || (dep1->sha256_contents != NULL && dep2->sha256_contents == NULL))
            return;
          if ((ind == 0 && strcmp (curr->sha1_contents, dep2->sha1_contents) > 0)
               || (ind == 1
		   && strcmp (curr->sha256_contents, dep2->sha256_contents) > 0))
            curr = dep2;
        }

      if (strcmp (curr->name, dep1->name) != 0)
        {
	  char *temp_name = (char *) xcalloc (1, sizeof (char));
	  char *temp_sha1_contents = NULL;
	  if (dep1->sha1_contents != NULL)
	    temp_sha1_contents = (char *) xcalloc (1, sizeof (char));
	  char *temp_sha256_contents = NULL;
	  if (dep1->sha256_contents != NULL)
	    temp_sha256_contents = (char *) xcalloc (1, sizeof (char));

          omnibor_set_contents (&temp_name, dep1->name,
				strlen (dep1->name));
          if (dep1->sha1_contents != NULL)
            omnibor_set_contents (&temp_sha1_contents, dep1->sha1_contents,
				  2 * GITOID_LENGTH_SHA1);
          if (dep1->sha256_contents != NULL)
	    omnibor_set_contents (&temp_sha256_contents, dep1->sha256_contents,
				  2 * GITOID_LENGTH_SHA256);

          omnibor_set_contents (&dep1->name, curr->name,
				strlen (curr->name));
          if (dep1->sha1_contents != NULL)
	    omnibor_set_contents (&dep1->sha1_contents, curr->sha1_contents,
				  2 * GITOID_LENGTH_SHA1);
          if (dep1->sha256_contents != NULL)
	    omnibor_set_contents (&dep1->sha256_contents, curr->sha256_contents,
				  2 * GITOID_LENGTH_SHA256);

          omnibor_set_contents (&curr->name, temp_name,
				strlen (temp_name));
          if (dep1->sha1_contents != NULL)
	    omnibor_set_contents (&curr->sha1_contents, temp_sha1_contents,
				  2 * GITOID_LENGTH_SHA1);
          if (dep1->sha256_contents != NULL)
	    omnibor_set_contents (&curr->sha256_contents, temp_sha256_contents,
				  2 * GITOID_LENGTH_SHA256);

	  if (dep1->sha256_contents != NULL)
	    free (temp_sha256_contents);
	  if (dep1->sha1_contents != NULL)
	    free (temp_sha1_contents);
	  free (temp_name);
        }
    }
}

/* OmniBOR ".note.omnibor" section struct which contains the filename of the
   dependency and the contents of its ".note.omnibor" section (the SHA1 gitoid
   and the SHA256 gitoid).  */

struct omnibor_note_sections
{
  struct omnibor_note_sections *next;
  char *name;
  char *sha1_contents;
  char *sha256_contents;
};

struct omnibor_note_sections *omnibor_note_sections_head,
			     *omnibor_note_sections_tail;

void
omnibor_add_to_note_sections (const char *filename, char *sha1_sec_contents,
			      char *sha256_sec_contents,
			      unsigned long sha1_sec_contents_len,
			      unsigned long sha256_sec_contents_len)
{
  struct omnibor_note_sections *elem
    = (struct omnibor_note_sections *) xmalloc (sizeof (*elem));
  elem->name = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&elem->name, filename, strlen (elem->name),
			    strlen (filename));
  if (sha1_sec_contents != NULL)
    {
      elem->sha1_contents = (char *) xcalloc (1, sizeof (char));
      omnibor_append_to_string (&elem->sha1_contents, sha1_sec_contents,
				strlen (elem->sha1_contents),
				sha1_sec_contents_len);
    }
  else
    elem->sha1_contents = NULL;
  if (sha256_sec_contents != NULL)
    {
      elem->sha256_contents = (char *) xcalloc (1, sizeof (char));
      omnibor_append_to_string (&elem->sha256_contents, sha256_sec_contents,
				strlen (elem->sha256_contents),
				sha256_sec_contents_len);
    }
  else
    elem->sha256_contents = NULL;
  elem->next = NULL;
  if (omnibor_note_sections_head == NULL)
    omnibor_note_sections_head = elem;
  else
    omnibor_note_sections_tail->next = elem;
  omnibor_note_sections_tail = elem;
}

static void
omnibor_clear_note_sections (void)
{
  struct omnibor_note_sections *dep = omnibor_note_sections_head, *old = NULL;
  while (dep != NULL)
    {
      free (dep->name);
      if (dep->sha1_contents)
        free (dep->sha1_contents);
      if (dep->sha256_contents)
        free (dep->sha256_contents);
      old = dep;
      dep = dep->next;
      free (old);
    }

  omnibor_note_sections_head = NULL;
  omnibor_note_sections_tail = NULL;
}

/* If the dependency with the given name is not in the omnibor_note_sections_head
   list, return NULL.  Otherwise, return the SHA1 gitoid (hash_func_type == 0)
   or the SHA256 gitoid (hash_func_type == 1) for that dependency.  If any value
   other than 0 or 1 is passed in hash_func_type, the behaviour is undefined.  */

static char *
omnibor_is_note_section_present (const char *name, unsigned hash_func_type)
{
  struct omnibor_note_sections *note;
  for (note = omnibor_note_sections_head; note != NULL; note = note->next)
    if (strcmp (name, note->name) == 0)
      {
        if (hash_func_type == 0)
          return note->sha1_contents;
        else if (hash_func_type == 1)
          return note->sha256_contents;
        /* This point should never be reached.  */
        else
          return NULL;
      }

  return NULL;
}

/* Create a file containing the metadata for the linking process in the
   OmniBOR context.  Parameter hash_func must be either 0 (for SHA1
   hash function) or 1 (for SHA256 hash function), otherwise the
   behaviour is undefined.  */

static bool
create_omnibor_metadata_file (const char *filename, unsigned hash_func)
{
  if (hash_func != 0 && hash_func != 1)
    return false;

  FILE *metadata_file = fopen (filename, "w");
  if (metadata_file != NULL)
    {
      char outfile_name_abs[PATH_MAX];
      realpath (output_filename, outfile_name_abs);
      fwrite ("outfile: path: ", sizeof (char), strlen ("outfile: path: "),
	      metadata_file);
      fwrite (outfile_name_abs, sizeof (char), strlen (outfile_name_abs),
	      metadata_file);
      fwrite ("\n", sizeof (char), strlen ("\n"), metadata_file);

      struct omnibor_deps *dep_file;
      for (dep_file = omnibor_deps_head; dep_file != NULL;
	   dep_file = dep_file->next)
	{
	  char *dep_line = (char *) xcalloc (1, sizeof (char));

	  char dep_name_abs[PATH_MAX];
	  realpath (dep_file->name, dep_name_abs);
	  omnibor_append_to_string (&dep_line, "infile: ",
				    strlen (dep_line),
				    strlen ("infile: "));
	  /* Save current length of dep_line before characters from hash
	     are added to the path.  This is done because the calculation
	     of the length of dep_line from here moving forward is done
	     manually by adding the length of the following parts of
	     dep_line since hash can produce '\0' characters, so strlen
	     is not good enough.  */
	  unsigned long dep_line_length = strlen (dep_line);
	  if (hash_func == 0)
	    {
	      omnibor_append_to_string (&dep_line, dep_file->sha1_contents,
					dep_line_length,
					2 * GITOID_LENGTH_SHA1);
	      dep_line_length += 2 * GITOID_LENGTH_SHA1;
	    }
	  else
	    {
	      omnibor_append_to_string (&dep_line, dep_file->sha256_contents,
					dep_line_length,
					2 * GITOID_LENGTH_SHA256);
	      dep_line_length += 2 * GITOID_LENGTH_SHA256;
	    }
	  omnibor_append_to_string (&dep_line, " path: ", dep_line_length,
				    strlen (" path: "));
	  dep_line_length += strlen (" path: ");
	  omnibor_append_to_string (&dep_line, dep_name_abs, dep_line_length,
				    strlen (dep_name_abs));
	  dep_line_length += strlen (dep_name_abs);
	  omnibor_append_to_string (&dep_line, "\n", dep_line_length,
				    strlen ("\n"));
	  dep_line_length += strlen ("\n");

	  fwrite (dep_line, sizeof (char), dep_line_length, metadata_file);

	  free (dep_line);
	}

      fwrite ("build_cmd: not available\n", sizeof (char),
	      strlen ("build_cmd: not available\n"),
	      metadata_file);

      fclose (metadata_file);
    }
  else
    return false;

  return true;
}

/* Store the OmniBOR information in the specified directory whose path is
   written in the result_dir parameter.  The hash_size parameter has to be
   either GITOID_LENGTH_SHA1 (for the SHA1 OmniBOR information) or
   GITOID_LENGTH_SHA256 (for the SHA256 OmniBOR information).  If any error
   occurs during the creation of the OmniBOR Document file, name parameter
   is set to point to an empty string.  */

static void
create_omnibor_document_file (char **name, const char *result_dir,
			      char *new_file_contents, unsigned int new_file_size,
			      unsigned int hash_size)
{
  if (hash_size != GITOID_LENGTH_SHA1 && hash_size != GITOID_LENGTH_SHA256)
    {
      omnibor_set_contents (name, "", 0);
      return;
    }

  char *path_objects = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&path_objects, "objects", strlen (path_objects),
			    strlen ("objects"));
  DIR *dir_one = NULL;

  if (result_dir)
    {
      if ((dir_one = opendir (result_dir)) == NULL)
        {
          mkdir (result_dir, S_IRWXU);
	  dir_one = opendir (result_dir);
	}

      if (dir_one != NULL)
        {
          omnibor_add_prefix_to_string (&path_objects, "/");
          omnibor_add_prefix_to_string (&path_objects, result_dir);
          int dfd1 = dirfd (dir_one);
          mkdirat (dfd1, "objects", S_IRWXU);
        }
      else if (strlen (result_dir) != 0)
        {
          DIR *final_dir = open_all_directories_in_path (result_dir);
          /* If an error occurred, illegal path is detected and the OmniBOR
             information is not written.  */
          /* TODO: Maybe put a message here that a specified path, in which
	     the OmniBOR information should be stored, is illegal.  */
	  /* TODO: In case of an error, if any directories were created,
	     remove them.  */
          if (final_dir == NULL)
            {
              close_all_directories_in_path ();
              free (path_objects);
              omnibor_set_contents (name, "", 0);
              return;
            }
          else
            {
              omnibor_add_prefix_to_string (&path_objects, "/");
	      omnibor_add_prefix_to_string (&path_objects, result_dir);
              int dfd1 = dirfd (final_dir);
              mkdirat (dfd1, "objects", S_IRWXU);
            }
        }
      /* This point should not be reachable.  */
      else
	{
	  free (path_objects);
	  omnibor_set_contents (name, "", 0);
	  return;
	}
    }
  /* This point should not be reachable.  */
  else
    {
      free (path_objects);
      omnibor_set_contents (name, "", 0);
      return;
    }

  DIR *dir_two = opendir (path_objects);
  if (dir_two == NULL)
    {
      close_all_directories_in_path ();
      if (result_dir && dir_one)
        closedir (dir_one);
      free (path_objects);
      omnibor_set_contents (name, "", 0);
      return;
    }

  int dfd2 = dirfd (dir_two);

  char *path_sha = NULL;
  DIR *dir_three = NULL;
  if (hash_size == GITOID_LENGTH_SHA1)
    {
      mkdirat (dfd2, "gitoid_blob_sha1", S_IRWXU);

      path_sha = (char *) xcalloc (1, sizeof (char));
      omnibor_append_to_string (&path_sha, path_objects, strlen (path_sha),
				strlen (path_objects));
      omnibor_append_to_string (&path_sha, "/gitoid_blob_sha1",
				strlen (path_sha),
				strlen ("/gitoid_blob_sha1"));
      dir_three = opendir (path_sha);
      if (dir_three == NULL)
        {
          closedir (dir_two);
          close_all_directories_in_path ();
          if (result_dir && dir_one)
            closedir (dir_one);
          free (path_sha);
          free (path_objects);
          omnibor_set_contents (name, "", 0);
          return;
        }
    }
  else
    {
      mkdirat (dfd2, "gitoid_blob_sha256", S_IRWXU);

      path_sha = (char *) xcalloc (1, sizeof (char));
      omnibor_append_to_string (&path_sha, path_objects, strlen (path_sha),
				strlen (path_objects));
      omnibor_append_to_string (&path_sha, "/gitoid_blob_sha256",
				strlen (path_sha),
				strlen ("/gitoid_blob_sha256"));
      dir_three = opendir (path_sha);
      if (dir_three == NULL)
        {
          closedir (dir_two);
          close_all_directories_in_path ();
          if (result_dir && dir_one)
            closedir (dir_one);
          free (path_sha);
          free (path_objects);
          omnibor_set_contents (name, "", 0);
          return;
        }
    }

  int dfd3 = dirfd (dir_three);
  char *name_substr = (char *) xcalloc (1, sizeof (char));
  omnibor_substr (&name_substr, 0, 2, *name);
  mkdirat (dfd3, name_substr, S_IRWXU);

  char *path_dir = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&path_dir, path_sha, strlen (path_dir),
			    strlen (path_sha));
  omnibor_append_to_string (&path_dir, "/", strlen (path_dir),
			    strlen ("/"));

  /* Save current length of path_dir before characters from hash are added to
     the path.  This is done because the calculation of the length of the path
     from here moving forward is done manually by adding the length of the
     following parts of the path since hash can produce '\0' characters, so
     strlen is not good enough.  */
  unsigned long path_dir_temp_len = strlen (path_dir);

  omnibor_append_to_string (&path_dir, name_substr, path_dir_temp_len, 2);
  DIR *dir_four = opendir (path_dir);
  if (dir_four == NULL)
    {
      closedir (dir_three);
      closedir (dir_two);
      close_all_directories_in_path ();
      if (result_dir && dir_one)
        closedir (dir_one);
      free (path_dir);
      free (name_substr);
      free (path_sha);
      free (path_objects);
      omnibor_set_contents (name, "", 0);
      return;
    }

  char *new_file_path = (char *) xcalloc (1, sizeof (char));
  omnibor_substr (&name_substr, 2, 2 * hash_size - 2, *name);
  omnibor_append_to_string (&new_file_path, path_dir, strlen (new_file_path),
			    path_dir_temp_len + 2);
  omnibor_append_to_string (&new_file_path, "/", path_dir_temp_len + 2,
			    strlen ("/"));
  omnibor_append_to_string (&new_file_path, name_substr,
			    path_dir_temp_len + 2 + strlen ("/"),
			    2 * hash_size - 2);

  FILE *new_file = fopen (new_file_path, "w");
  if (new_file != NULL)
    {
      fwrite (new_file_contents, sizeof (char), new_file_size, new_file);
      fclose (new_file);
    }
  else
    omnibor_set_contents (name, "", 0);

  omnibor_append_to_string (&new_file_path, ".metadata",
			    path_dir_temp_len + strlen ("/") + 2 * hash_size,
			    strlen (".metadata"));
  if (!create_omnibor_metadata_file (new_file_path,
				     hash_size == GITOID_LENGTH_SHA1 ? 0 : 1))
    omnibor_set_contents (name, "", 0);

  closedir (dir_four);
  closedir (dir_three);
  closedir (dir_two);
  close_all_directories_in_path ();
  if (result_dir && dir_one)
    closedir (dir_one);
  free (new_file_path);
  free (path_dir);
  free (name_substr);
  free (path_sha);
  free (path_objects);
}

/* Calculate the gitoids of all the dependencies of the resulting executable
   and create the OmniBOR Document file using them.  Then calculate the
   gitoid of that file and name it with that gitoid in the format specified
   by the OmniBOR specification.  Use SHA1 hashing algorithm for calculating
   all the gitoids.  */

static void
write_sha1_omnibor (char **name, const char *result_dir)
{
  static const char *const lut = "0123456789abcdef";
  char *new_file_contents = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&new_file_contents, "gitoid:blob:sha1\n",
			    strlen (new_file_contents),
			    strlen ("gitoid:blob:sha1\n"));
  char *temp_file_contents = (char *) xcalloc (1, sizeof (char));
  char *high_ch = (char *) xmalloc (sizeof (char) * 2);
  high_ch[1] = '\0';
  char *low_ch = (char *) xmalloc (sizeof (char) * 2);
  low_ch[1] = '\0';

  struct omnibor_deps *curr_dep = NULL;
  struct dependency_file *dep;
  for (dep = dependency_files; dep != NULL; dep = dep->next)
    {
      if ((curr_dep = omnibor_is_dep_present (dep->name)) != NULL)
	if (curr_dep->sha1_contents != NULL)
	  continue;

      FILE *dep_file_handle = fopen (dep->name, "rb");
      if (dep_file_handle == NULL)
	continue;
      unsigned char resblock[GITOID_LENGTH_SHA1];

      calculate_sha1_omnibor (dep_file_handle, resblock);

      fclose (dep_file_handle);

      omnibor_set_contents (&temp_file_contents, "", 0);

      for (unsigned i = 0; i != GITOID_LENGTH_SHA1; i++)
        {
          high_ch[0] = lut[resblock[i] >> 4];
          low_ch[0] = lut[resblock[i] & 15];
          omnibor_append_to_string (&temp_file_contents, high_ch,
				    i * 2, 2);
          omnibor_append_to_string (&temp_file_contents, low_ch,
				    i * 2 + 1, 2);
        }

      if (curr_dep == NULL)
        omnibor_add_to_deps (dep->name, temp_file_contents, NULL,
			     2 * GITOID_LENGTH_SHA1, 0);
      /* Here curr_dep->sha1_contents has to be NULL.  */
      else
        {
          curr_dep->sha1_contents = (char *) xcalloc (1, sizeof (char));
	  omnibor_append_to_string (&curr_dep->sha1_contents,
				    temp_file_contents,
				    strlen (curr_dep->sha1_contents),
				    2 * GITOID_LENGTH_SHA1);
        }
    }

  omnibor_sort (0);

  unsigned current_length = strlen (new_file_contents);
  struct omnibor_deps *dep_file;
  for (dep_file = omnibor_deps_head; dep_file != NULL;
       dep_file = dep_file->next)
    {
      omnibor_append_to_string (&new_file_contents, "blob ",
				current_length,
				strlen ("blob "));
      current_length += strlen ("blob ");
      omnibor_append_to_string (&new_file_contents, dep_file->sha1_contents,
				current_length,
				2 * GITOID_LENGTH_SHA1);
      current_length += 2 * GITOID_LENGTH_SHA1;
      char *note_sec_contents = omnibor_is_note_section_present (dep_file->name, 0);
      if (note_sec_contents != NULL)
        {
          omnibor_append_to_string (&new_file_contents, " bom ",
				    current_length,
				    strlen (" bom "));
          current_length += strlen (" bom ");
	  omnibor_append_to_string (&new_file_contents, note_sec_contents,
				    current_length,
				    2 * GITOID_LENGTH_SHA1);
          current_length += 2 * GITOID_LENGTH_SHA1;
        }
      omnibor_append_to_string (&new_file_contents, "\n",
				current_length,
				strlen ("\n"));
      current_length += strlen ("\n");
    }
  unsigned new_file_size = current_length;

  unsigned char resblock[GITOID_LENGTH_SHA1];
  calculate_sha1_omnibor_with_contents (new_file_contents, resblock);

  for (unsigned i = 0; i != GITOID_LENGTH_SHA1; i++)
    {
      high_ch[0] = lut[resblock[i] >> 4];
      low_ch[0] = lut[resblock[i] & 15];
      omnibor_append_to_string (name, high_ch, i * 2, 2);
      omnibor_append_to_string (name, low_ch, i * 2 + 1, 2);
    }
  free (low_ch);
  free (high_ch);

  create_omnibor_document_file (name, result_dir, new_file_contents,
				new_file_size, GITOID_LENGTH_SHA1);

  free (temp_file_contents);
  free (new_file_contents);
}

/* Calculate the gitoids of all the dependencies of the resulting executable
   and create the OmniBOR Document file using them.  Then calculate the
   gitoid of that file and name it with that gitoid in the format specified
   by the OmniBOR specification.  Use SHA256 hashing algorithm for calculating
   all the gitoids.  */

static void
write_sha256_omnibor (char **name, const char *result_dir)
{
  static const char *const lut = "0123456789abcdef";
  char *new_file_contents = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&new_file_contents, "gitoid:blob:sha256\n",
			    strlen (new_file_contents),
			    strlen ("gitoid:blob:sha256\n"));
  char *temp_file_contents = (char *) xcalloc (1, sizeof (char));
  char *high_ch = (char *) xmalloc (sizeof (char) * 2);
  high_ch[1] = '\0';
  char *low_ch = (char *) xmalloc (sizeof (char) * 2);
  low_ch[1] = '\0';

  struct omnibor_deps *curr_dep = NULL;
  struct dependency_file *dep;
  for (dep = dependency_files; dep != NULL; dep = dep->next)
    {
      if ((curr_dep = omnibor_is_dep_present (dep->name)) != NULL)
	if (curr_dep->sha256_contents != NULL)
	  continue;

      FILE *dep_file_handle = fopen (dep->name, "rb");
      if (dep_file_handle == NULL)
	continue;
      unsigned char resblock[GITOID_LENGTH_SHA256];

      calculate_sha256_omnibor (dep_file_handle, resblock);

      fclose (dep_file_handle);

      omnibor_set_contents (&temp_file_contents, "", 0);

      for (unsigned i = 0; i != GITOID_LENGTH_SHA256; i++)
        {
          high_ch[0] = lut[resblock[i] >> 4];
          low_ch[0] = lut[resblock[i] & 15];
          omnibor_append_to_string (&temp_file_contents, high_ch,
				    i * 2, 2);
          omnibor_append_to_string (&temp_file_contents, low_ch,
				    i * 2 + 1, 2);
        }

      if (curr_dep == NULL)
        omnibor_add_to_deps (dep->name, NULL, temp_file_contents,
			     0, 2 * GITOID_LENGTH_SHA256);
      /* Here curr_dep->sha256_contents has to be NULL.  */
      else
        {
          curr_dep->sha256_contents = (char *) xcalloc (1, sizeof (char));
	  omnibor_append_to_string (&curr_dep->sha256_contents,
				    temp_file_contents,
				    strlen (curr_dep->sha256_contents),
				    2 * GITOID_LENGTH_SHA256);
        }
    }

  omnibor_sort (1);

  unsigned current_length = strlen (new_file_contents);
  struct omnibor_deps *dep_file;
  for (dep_file = omnibor_deps_head; dep_file != NULL;
       dep_file = dep_file->next)
    {
      omnibor_append_to_string (&new_file_contents, "blob ",
				current_length,
				strlen ("blob "));
      current_length += strlen ("blob ");
      omnibor_append_to_string (&new_file_contents, dep_file->sha256_contents,
				current_length,
				2 * GITOID_LENGTH_SHA256);
      current_length += 2 * GITOID_LENGTH_SHA256;
      char *note_sec_contents = omnibor_is_note_section_present (dep_file->name, 1);
      if (note_sec_contents != NULL)
        {
          omnibor_append_to_string (&new_file_contents, " bom ",
				    current_length,
				    strlen (" bom "));
          current_length += strlen (" bom ");
	  omnibor_append_to_string (&new_file_contents, note_sec_contents,
				    current_length,
				    2 * GITOID_LENGTH_SHA256);
          current_length += 2 * GITOID_LENGTH_SHA256;
        }
      omnibor_append_to_string (&new_file_contents, "\n",
				current_length,
				strlen ("\n"));
      current_length += strlen ("\n");
    }
  unsigned new_file_size = current_length;

  unsigned char resblock[GITOID_LENGTH_SHA256];
  calculate_sha256_omnibor_with_contents (new_file_contents, resblock);

  for (unsigned i = 0; i != GITOID_LENGTH_SHA256; i++)
    {
      high_ch[0] = lut[resblock[i] >> 4];
      low_ch[0] = lut[resblock[i] & 15];
      omnibor_append_to_string (name, high_ch, i * 2, 2);
      omnibor_append_to_string (name, low_ch, i * 2 + 1, 2);
    }
  free (low_ch);
  free (high_ch);

  create_omnibor_document_file (name, result_dir, new_file_contents,
				new_file_size, GITOID_LENGTH_SHA256);

  free (temp_file_contents);
  free (new_file_contents);
}

/* Create the file which connects the SHA1 OmniBOR Document file for the
   output file and the SHA1 id of that output file.  */

static void
omnibor_create_file_no_embed_sha1 (const char *gitoid_sha1, char *res_dir)
{
  static const char *const lut = "0123456789abcdef";
  char *gitoid_exec_sha1 = (char *) xcalloc (1, sizeof (char));
  char *high_ch = (char *) xmalloc (sizeof (char) * 2);
  high_ch[1] = '\0';
  char *low_ch = (char *) xmalloc (sizeof (char) * 2);
  low_ch[1] = '\0';

  FILE *file_executable = fopen (output_filename, "rb");
  if (file_executable == NULL)
    {
      free (low_ch);
      free (high_ch);
      free (gitoid_exec_sha1);
      return;
    }
  unsigned char resblock[GITOID_LENGTH_SHA1];

  calculate_sha1_omnibor (file_executable, resblock);

  fclose (file_executable);

  for (unsigned i = 0; i != GITOID_LENGTH_SHA1; i++)
    {
      high_ch[0] = lut[resblock[i] >> 4];
      low_ch[0] = lut[resblock[i] & 15];
      omnibor_append_to_string (&gitoid_exec_sha1, high_ch, i * 2, 2);
      omnibor_append_to_string (&gitoid_exec_sha1, low_ch, i * 2 + 1, 2);
    }

  char *path_mapping = (char *) xcalloc (1, sizeof (char));
  DIR *dir = NULL, *dir_mapping = NULL;

  if (strcmp ("", res_dir) != 0)
    {
      dir = opendir (res_dir);
      if (dir == NULL)
	{
	  free (path_mapping);
	  free (low_ch);
	  free (high_ch);
	  free (gitoid_exec_sha1);
	  return;
	}

      int dfd = dirfd (dir);
      mkdirat (dfd, "mapping", S_IRWXU);
      omnibor_append_to_string (&path_mapping, res_dir, strlen (path_mapping),
				strlen (res_dir));
      omnibor_append_to_string (&path_mapping, "/mapping", strlen (path_mapping),
				strlen ("/mapping"));
    }
  /* This point should not be reachable.  */
  else
    {
      free (path_mapping);
      free (low_ch);
      free (high_ch);
      free (gitoid_exec_sha1);
      return;
    }

  dir_mapping = opendir (path_mapping);
  if (dir_mapping == NULL)
    {
      if (strcmp ("", res_dir) != 0)
	closedir (dir);
      free (path_mapping);
      free (low_ch);
      free (high_ch);
      free (gitoid_exec_sha1);
      return;
    }

  int dfd_mapping = dirfd (dir_mapping);
  mkdirat (dfd_mapping, "gitoid_blob_sha1", S_IRWXU);

  char *path_sha = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&path_sha, path_mapping, strlen (path_sha),
			    strlen (path_mapping));
  omnibor_append_to_string (&path_sha, "/gitoid_blob_sha1",
			    strlen (path_sha),
			    strlen ("/gitoid_blob_sha1"));
  DIR *dir_sha = opendir (path_sha);
  if (dir_sha == NULL)
    {
      closedir (dir_mapping);
      if (strcmp ("", res_dir) != 0)
	closedir (dir);
      free (path_sha);
      free (path_mapping);
      free (low_ch);
      free (high_ch);
      free (gitoid_exec_sha1);
      return;
    }

  char *new_file_path = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&new_file_path, path_sha, strlen (new_file_path),
			    strlen (path_sha));
  omnibor_append_to_string (&new_file_path, "/", strlen (new_file_path),
			    strlen ("/"));
  omnibor_append_to_string (&new_file_path, gitoid_exec_sha1, strlen (new_file_path),
			    2 * GITOID_LENGTH_SHA1);

  FILE *new_file = fopen (new_file_path, "w");
  if (new_file != NULL)
    {
      fwrite (gitoid_sha1, sizeof (char), 2 * GITOID_LENGTH_SHA1, new_file);
      fwrite ("\n", sizeof (char), 1, new_file);
      fclose (new_file);
    }

  closedir (dir_sha);
  closedir (dir_mapping);
  if (strcmp ("", res_dir) != 0)
    closedir (dir);
  free (new_file_path);
  free (path_sha);
  free (path_mapping);
  free (low_ch);
  free (high_ch);
  free (gitoid_exec_sha1);
}

/* Create the file which connects the SHA256 OmniBOR Document file for the
   output file and the SHA256 id of that output file.  */

static void
omnibor_create_file_no_embed_sha256 (const char *gitoid_sha256, char *res_dir)
{
  static const char *const lut = "0123456789abcdef";
  char *gitoid_exec_sha256 = (char *) xcalloc (1, sizeof (char));
  char *high_ch = (char *) xmalloc (sizeof (char) * 2);
  high_ch[1] = '\0';
  char *low_ch = (char *) xmalloc (sizeof (char) * 2);
  low_ch[1] = '\0';

  FILE *file_executable = fopen (output_filename, "rb");
  if (file_executable == NULL)
    {
      free (low_ch);
      free (high_ch);
      free (gitoid_exec_sha256);
      return;
    }
  unsigned char resblock[GITOID_LENGTH_SHA256];

  calculate_sha256_omnibor (file_executable, resblock);

  fclose (file_executable);

  for (unsigned i = 0; i != GITOID_LENGTH_SHA256; i++)
    {
      high_ch[0] = lut[resblock[i] >> 4];
      low_ch[0] = lut[resblock[i] & 15];
      omnibor_append_to_string (&gitoid_exec_sha256, high_ch, i * 2, 2);
      omnibor_append_to_string (&gitoid_exec_sha256, low_ch, i * 2 + 1, 2);
    }

  char *path_mapping = (char *) xcalloc (1, sizeof (char));
  DIR *dir = NULL, *dir_mapping = NULL;

  if (strcmp ("", res_dir) != 0)
    {
      dir = opendir (res_dir);
      if (dir == NULL)
	{
	  free (path_mapping);
	  free (low_ch);
	  free (high_ch);
	  free (gitoid_exec_sha256);
	  return;
	}

      int dfd = dirfd (dir);
      mkdirat (dfd, "mapping", S_IRWXU);
      omnibor_append_to_string (&path_mapping, res_dir, strlen (path_mapping),
				strlen (res_dir));
      omnibor_append_to_string (&path_mapping, "/mapping", strlen (path_mapping),
				strlen ("/mapping"));
    }
  /* This point should not be reachable.  */
  else
    {
      free (path_mapping);
      free (low_ch);
      free (high_ch);
      free (gitoid_exec_sha256);
      return;
    }

  dir_mapping = opendir (path_mapping);
  if (dir_mapping == NULL)
    {
      if (strcmp ("", res_dir) != 0)
	closedir (dir);
      free (path_mapping);
      free (low_ch);
      free (high_ch);
      free (gitoid_exec_sha256);
      return;
    }

  int dfd_mapping = dirfd (dir_mapping);
  mkdirat (dfd_mapping, "gitoid_blob_sha256", S_IRWXU);

  char *path_sha = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&path_sha, path_mapping, strlen (path_sha),
			    strlen (path_mapping));
  omnibor_append_to_string (&path_sha, "/gitoid_blob_sha256",
			    strlen (path_sha),
			    strlen ("/gitoid_blob_sha256"));
  DIR *dir_sha = opendir (path_sha);
  if (dir_sha == NULL)
    {
      closedir (dir_mapping);
      if (strcmp ("", res_dir) != 0)
	closedir (dir);
      free (path_sha);
      free (path_mapping);
      free (low_ch);
      free (high_ch);
      free (gitoid_exec_sha256);
      return;
    }

  char *new_file_path = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&new_file_path, path_sha, strlen (new_file_path),
			    strlen (path_sha));
  omnibor_append_to_string (&new_file_path, "/", strlen (new_file_path),
			    strlen ("/"));
  omnibor_append_to_string (&new_file_path, gitoid_exec_sha256, strlen (new_file_path),
			    2 * GITOID_LENGTH_SHA256);

  FILE *new_file = fopen (new_file_path, "w");
  if (new_file != NULL)
    {
      fwrite (gitoid_sha256, sizeof (char), 2 * GITOID_LENGTH_SHA256, new_file);
      fwrite ("\n", sizeof (char), 1, new_file);
      fclose (new_file);
    }

  closedir (dir_sha);
  closedir (dir_mapping);
  if (strcmp ("", res_dir) != 0)
    closedir (dir);
  free (new_file_path);
  free (path_sha);
  free (path_mapping);
  free (low_ch);
  free (high_ch);
  free (gitoid_exec_sha256);
}


static void
ld_cleanup (void)
{
  bfd_cache_close_all ();
#if BFD_SUPPORTS_PLUGINS
  plugin_call_cleanup ();
#endif
  if (output_filename && delete_output_file_on_failure)
    unlink_if_ordinary (output_filename);
}

/* Hook to notice BFD assertions.  */

static void
ld_bfd_assert_handler (const char *fmt, const char *bfdver,
		       const char *file, int line)
{
  config.make_executable = false;
  (*default_bfd_assert_handler) (fmt, bfdver, file, line);
}

/* Hook the bfd error/warning handler for --fatal-warnings.  */

static void
ld_bfd_error_handler (const char *fmt, va_list ap)
{
  if (config.fatal_warnings)
    config.make_executable = false;
  (*default_bfd_error_handler) (fmt, ap);
}

int
main (int argc, char **argv)
{
  char *emulation;
  long start_time = get_run_time ();

#ifdef HAVE_LC_MESSAGES
  setlocale (LC_MESSAGES, "");
#endif
  setlocale (LC_CTYPE, "");
  bindtextdomain (PACKAGE, LOCALEDIR);
  textdomain (PACKAGE);

  program_name = argv[0];
  xmalloc_set_program_name (program_name);

  START_PROGRESS (program_name, 0);

  expandargv (&argc, &argv);

  if (bfd_init () != BFD_INIT_MAGIC)
    einfo (_("%F%P: fatal error: libbfd ABI mismatch\n"));

  bfd_set_error_program_name (program_name);

  /* We want to notice and fail on those nasty BFD assertions which are
     likely to signal incorrect output being generated but otherwise may
     leave no trace.  */
  default_bfd_assert_handler = bfd_set_assert_handler (ld_bfd_assert_handler);

  /* Also hook the bfd error/warning handler for --fatal-warnings.  */
  default_bfd_error_handler = bfd_set_error_handler (ld_bfd_error_handler);

  xatexit (ld_cleanup);

  /* Set up the sysroot directory.  */
  ld_sysroot = get_sysroot (argc, argv);
  if (*ld_sysroot)
    ld_canon_sysroot = lrealpath (ld_sysroot);
  if (ld_canon_sysroot)
    {
      ld_canon_sysroot_len = strlen (ld_canon_sysroot);

      /* is_sysrooted_pathname() relies on no trailing dirsep.  */
      if (ld_canon_sysroot_len > 0
	  && IS_DIR_SEPARATOR (ld_canon_sysroot [ld_canon_sysroot_len - 1]))
	ld_canon_sysroot [--ld_canon_sysroot_len] = '\0';
    }
  else
    ld_canon_sysroot_len = -1;

  /* Set the default BFD target based on the configured target.  Doing
     this permits the linker to be configured for a particular target,
     and linked against a shared BFD library which was configured for
     a different target.  The macro TARGET is defined by Makefile.  */
  if (!bfd_set_default_target (TARGET))
    {
      einfo (_("%X%P: can't set BFD default target to `%s': %E\n"), TARGET);
      xexit (1);
    }

#if YYDEBUG
  {
    extern int yydebug;
    yydebug = 1;
  }
#endif

  config.build_constructors = true;
  config.rpath_separator = ':';
  config.split_by_reloc = (unsigned) -1;
  config.split_by_file = (bfd_size_type) -1;
  config.make_executable = true;
  config.magic_demand_paged = true;
  config.text_read_only = true;
  config.print_map_discarded = true;
  link_info.disable_target_specific_optimizations = -1;

  command_line.warn_mismatch = true;
  command_line.warn_search_mismatch = true;
  command_line.check_section_addresses = -1;

  /* We initialize DEMANGLING based on the environment variable
     COLLECT_NO_DEMANGLE.  The gcc collect2 program will demangle the
     output of the linker, unless COLLECT_NO_DEMANGLE is set in the
     environment.  Acting the same way here lets us provide the same
     interface by default.  */
  demangling = getenv ("COLLECT_NO_DEMANGLE") == NULL;

  link_info.allow_undefined_version = true;
  link_info.keep_memory = true;
  link_info.max_cache_size = (bfd_size_type) -1;
  link_info.combreloc = true;
  link_info.strip_discarded = true;
  link_info.prohibit_multiple_definition_absolute = false;
  link_info.textrel_check = DEFAULT_LD_TEXTREL_CHECK;
  link_info.emit_hash = DEFAULT_EMIT_SYSV_HASH;
  link_info.emit_gnu_hash = DEFAULT_EMIT_GNU_HASH;
  link_info.callbacks = &link_callbacks;
  link_info.input_bfds_tail = &link_info.input_bfds;
  /* SVR4 linkers seem to set DT_INIT and DT_FINI based on magic _init
     and _fini symbols.  We are compatible.  */
  link_info.init_function = "_init";
  link_info.fini_function = "_fini";
  link_info.relax_pass = 1;
  link_info.extern_protected_data = -1;
  link_info.dynamic_undefined_weak = -1;
  link_info.indirect_extern_access = -1;
  link_info.pei386_auto_import = -1;
  link_info.spare_dynamic_tags = 5;
  link_info.path_separator = ':';
#ifdef DEFAULT_FLAG_COMPRESS_DEBUG
  link_info.compress_debug = COMPRESS_DEBUG_GABI_ZLIB;
#endif
#ifdef DEFAULT_NEW_DTAGS
  link_info.new_dtags = DEFAULT_NEW_DTAGS;
#endif
  link_info.start_stop_gc = false;
  link_info.start_stop_visibility = STV_PROTECTED;

  ldfile_add_arch ("");
  emulation = get_emulation (argc, argv);
  ldemul_choose_mode (emulation);
  default_target = ldemul_choose_target (argc, argv);
  lang_init ();
  ldexp_init ();
  ldemul_before_parse ();
  lang_has_input_file = false;
  parse_args (argc, argv);

  if (config.hash_table_size != 0)
    bfd_hash_set_default_size (config.hash_table_size);

#if BFD_SUPPORTS_PLUGINS
  /* Now all the plugin arguments have been gathered, we can load them.  */
  plugin_load_plugins ();
#endif /* BFD_SUPPORTS_PLUGINS */

  ldemul_set_symbols ();

  /* If we have not already opened and parsed a linker script,
     try the default script from command line first.  */
  if (saved_script_handle == NULL
      && command_line.default_script != NULL)
    {
      ldfile_open_script_file (command_line.default_script);
      parser_input = input_script;
      yyparse ();
    }

  /* If we have not already opened and parsed a linker script
     read the emulation's appropriate default script.  */
  if (saved_script_handle == NULL)
    {
      int isfile;
      char *s = ldemul_get_script (&isfile);

      if (isfile)
	ldfile_open_default_command_file (s);
      else
	{
	  lex_string = s;
	  lex_redirect (s, _("built in linker script"), 1);
	}
      parser_input = input_script;
      yyparse ();
      lex_string = NULL;
    }

  if (verbose)
    {
      if (saved_script_handle)
	info_msg (_("using external linker script:"));
      else
	info_msg (_("using internal linker script:"));
      info_msg ("\n==================================================\n");

      if (saved_script_handle)
	{
	  static const int ld_bufsz = 8193;
	  size_t n;
	  char *buf = (char *) xmalloc (ld_bufsz);

	  rewind (saved_script_handle);
	  while ((n = fread (buf, 1, ld_bufsz - 1, saved_script_handle)) > 0)
	    {
	      buf[n] = 0;
	      info_msg ("%s", buf);
	    }
	  rewind (saved_script_handle);
	  free (buf);
	}
      else
	{
	  int isfile;

	  info_msg (ldemul_get_script (&isfile));
	}

      info_msg ("\n==================================================\n");
    }

  if (command_line.force_group_allocation
      || !bfd_link_relocatable (&link_info))
    link_info.resolve_section_groups = true;
  else
    link_info.resolve_section_groups = false;

  if (command_line.print_output_format)
    info_msg ("%s\n", lang_get_output_target ());

  lang_final ();

  /* If the only command line argument has been -v or --version or --verbose
     then ignore any input files provided by linker scripts and exit now.
     We do not want to create an output file when the linker is just invoked
     to provide version information.  */
  if (argc == 2 && version_printed)
    xexit (0);

  if (link_info.inhibit_common_definition && !bfd_link_dll (&link_info))
    einfo (_("%F%P: --no-define-common may not be used without -shared\n"));

  if (!lang_has_input_file)
    {
      if (version_printed || command_line.print_output_format)
	xexit (0);
      einfo (_("%F%P: no input files\n"));
    }

  if (verbose)
    info_msg (_("%P: mode %s\n"), emulation);

  ldemul_after_parse ();

  if (config.map_filename)
    {
      if (strcmp (config.map_filename, "-") == 0)
	{
	  config.map_file = stdout;
	}
      else
	{
	  config.map_file = fopen (config.map_filename, FOPEN_WT);
	  if (config.map_file == (FILE *) NULL)
	    {
	      bfd_set_error (bfd_error_system_call);
	      einfo (_("%F%P: cannot open map file %s: %E\n"),
		     config.map_filename);
	    }
	}
      link_info.has_map_file = true;
    }

  lang_process ();

  /* Print error messages for any missing symbols, for any warning
     symbols, and possibly multiple definitions.  */
  if (bfd_link_relocatable (&link_info))
    link_info.output_bfd->flags &= ~EXEC_P;
  else
    link_info.output_bfd->flags |= EXEC_P;

  if ((link_info.compress_debug & COMPRESS_DEBUG))
    {
      link_info.output_bfd->flags |= BFD_COMPRESS;
      if (link_info.compress_debug == COMPRESS_DEBUG_GABI_ZLIB)
	link_info.output_bfd->flags |= BFD_COMPRESS_GABI;
    }

  ldwrite ();

  if (config.map_file != NULL)
    lang_map ();
  if (command_line.cref)
    output_cref (config.map_file != NULL ? config.map_file : stdout);
  if (nocrossref_list != NULL)
    check_nocrossrefs ();
  if (command_line.print_memory_usage)
    lang_print_memory_usage ();
#if 0
  {
    struct bfd_link_hash_entry *h;

    h = bfd_link_hash_lookup (link_info.hash, "__image_base__", 0,0,1);
    fprintf (stderr, "lookup = %p val %lx\n", h, h ? h->u.def.value : 1);
  }
#endif
  ldexp_finish ();
  lang_finish ();

  if (config.dependency_file != NULL)
    write_dependency_file ();

  /* If the calculation of the OmniBOR information is enabled, do it here.
     Also, determine the directory to store the OmniBOR files in this order of
     precedence.
	1. Use the directory name passed with --omnibor= option.
	2. Use the location set in OMNIBOR_DIR environment variable.  */
  if (config.omnibor_dir != NULL ||
     (getenv ("OMNIBOR_DIR") != NULL && strlen (getenv ("OMNIBOR_DIR")) > 0))
    {
      omnibor_dir = (char *) xcalloc (1, sizeof (char));

      if (config.omnibor_dir != NULL && strlen (config.omnibor_dir) > 0)
            omnibor_set_contents (&omnibor_dir, config.omnibor_dir,
				  strlen (config.omnibor_dir));

      if (strlen (omnibor_dir) == 0)
        {
	  const char *env_omnibor = getenv ("OMNIBOR_DIR");
	  if (env_omnibor != NULL)
	    omnibor_set_contents (&omnibor_dir, env_omnibor, strlen (env_omnibor));
        }

      char *gitoid_sha1 = (char *) xcalloc (1, sizeof (char));
      char *gitoid_sha256 = (char *) xcalloc (1, sizeof (char));
      if (strlen (omnibor_dir) > 0)
        {
          write_sha1_omnibor (&gitoid_sha1, omnibor_dir);
          write_sha256_omnibor (&gitoid_sha256, omnibor_dir);
        }
      /* This else should be unreachable.  */
      else
        {
          omnibor_set_contents (&gitoid_sha1, "", 0);
          omnibor_set_contents (&gitoid_sha256, "", 0);
        }

      omnibor_clear_deps ();
      omnibor_clear_note_sections ();

      if (strcmp ("", gitoid_sha1) == 0 || strcmp ("", gitoid_sha256) == 0)
        {
          if (ldelf_emit_note_omnibor_sha1 != NULL)
	    {
	      free (ldelf_emit_note_omnibor_sha1);
	      ldelf_emit_note_omnibor_sha1 = NULL;
	    }
	  if (ldelf_emit_note_omnibor_sha256 != NULL)
	    {
	      free (ldelf_emit_note_omnibor_sha256);
	      ldelf_emit_note_omnibor_sha256 = NULL;
	    }
	  free (gitoid_sha256);
	  free (gitoid_sha1);
	  free (omnibor_dir);
	  einfo (_("%P: Error in creation of OmniBOR Document files\n"));
	  xexit (1);
        }
      else
        {
	  memcpy (ldelf_emit_note_omnibor_sha1, gitoid_sha1, 2 * GITOID_LENGTH_SHA1);
	  ldelf_emit_note_omnibor_sha1[2 * GITOID_LENGTH_SHA1] = '\0';
	  memcpy (ldelf_emit_note_omnibor_sha256, gitoid_sha256,
		  2 * GITOID_LENGTH_SHA256);
	  ldelf_emit_note_omnibor_sha256[2 * GITOID_LENGTH_SHA256] = '\0';
	}

      free (gitoid_sha256);
      free (gitoid_sha1);
      if (getenv ("OMNIBOR_NO_EMBED") == NULL)
	free (omnibor_dir);
    }

  /* Even if we're producing relocatable output, some non-fatal errors should
     be reported in the exit status.  (What non-fatal errors, if any, do we
     want to ignore for relocatable output?)  */
  if (!config.make_executable && !force_make_executable)
    {
      if (verbose)
	einfo (_("%P: link errors found, deleting executable `%s'\n"),
	       output_filename);

      /* The file will be removed by ld_cleanup.  */
      xexit (1);
    }
  else
    {
      if (!bfd_close (link_info.output_bfd))
	einfo (_("%F%P: %pB: final close failed: %E\n"), link_info.output_bfd);

      /* If the --force-exe-suffix is enabled, and we're making an
	 executable file and it doesn't end in .exe, copy it to one
	 which does.  */
      if (!bfd_link_relocatable (&link_info)
	  && command_line.force_exe_suffix)
	{
	  int len = strlen (output_filename);

	  if (len < 4
	      || (strcasecmp (output_filename + len - 4, ".exe") != 0
		  && strcasecmp (output_filename + len - 4, ".dll") != 0))
	    {
	      FILE *src;
	      FILE *dst;
	      const int bsize = 4096;
	      char *buf = (char *) xmalloc (bsize);
	      int l;
	      char *dst_name = (char *) xmalloc (len + 5);

	      strcpy (dst_name, output_filename);
	      strcat (dst_name, ".exe");
	      src = fopen (output_filename, FOPEN_RB);
	      dst = fopen (dst_name, FOPEN_WB);

	      if (!src)
		einfo (_("%F%P: unable to open for source of copy `%s'\n"),
		       output_filename);
	      if (!dst)
		einfo (_("%F%P: unable to open for destination of copy `%s'\n"),
		       dst_name);
	      while ((l = fread (buf, 1, bsize, src)) > 0)
		{
		  int done = fwrite (buf, 1, l, dst);

		  if (done != l)
		    einfo (_("%P: error writing file `%s'\n"), dst_name);
		}

	      fclose (src);
	      if (fclose (dst) == EOF)
		einfo (_("%P: error closing file `%s'\n"), dst_name);
	      free (dst_name);
	      free (buf);
	    }
	}
    }

  END_PROGRESS (program_name);

  if (config.stats)
    {
      long run_time = get_run_time () - start_time;

      fflush (stdout);
      fprintf (stderr, _("%s: total time in link: %ld.%06ld\n"),
	       program_name, run_time / 1000000, run_time % 1000000);
      fflush (stderr);
    }

  /* Create files which connect the output file to its OmniBOR Document
     files.  Do it only in the NO_EMBED case (when OMNIBOR_NO_EMBED
     environment variable is set).  */
  if (getenv ("OMNIBOR_NO_EMBED") != NULL)
    if (config.omnibor_dir != NULL ||
       (getenv ("OMNIBOR_DIR") != NULL && strlen (getenv ("OMNIBOR_DIR")) > 0))
      {
	omnibor_create_file_no_embed_sha1 (ldelf_emit_note_omnibor_sha1,
					   omnibor_dir);

	omnibor_create_file_no_embed_sha256 (ldelf_emit_note_omnibor_sha256,
					     omnibor_dir);

	free (ldelf_emit_note_omnibor_sha1);
	free (ldelf_emit_note_omnibor_sha256);
	ldelf_emit_note_omnibor_sha1 = NULL;
	ldelf_emit_note_omnibor_sha256 = NULL;
	free (omnibor_dir);
      }

  /* Prevent ld_cleanup from doing anything, after a successful link.  */
  output_filename = NULL;

  xexit (0);
  return 0;
}

/* If the configured sysroot is relocatable, try relocating it based on
   default prefix FROM.  Return the relocated directory if it exists,
   otherwise return null.  */

static char *
get_relative_sysroot (const char *from ATTRIBUTE_UNUSED)
{
#ifdef TARGET_SYSTEM_ROOT_RELOCATABLE
  char *path;
  struct stat s;

  path = make_relative_prefix (program_name, from, TARGET_SYSTEM_ROOT);
  if (path)
    {
      if (stat (path, &s) == 0 && S_ISDIR (s.st_mode))
	return path;
      free (path);
    }
#endif
  return 0;
}

/* Return the sysroot directory.  Return "" if no sysroot is being used.  */

static const char *
get_sysroot (int argc, char **argv)
{
  int i;
  const char *path = NULL;

  for (i = 1; i < argc; i++)
    if (startswith (argv[i], "--sysroot="))
      path = argv[i] + strlen ("--sysroot=");

  if (!path)
    path = get_relative_sysroot (BINDIR);

  if (!path)
    path = get_relative_sysroot (TOOLBINDIR);

  if (!path)
    path = TARGET_SYSTEM_ROOT;

  if (IS_DIR_SEPARATOR (*path) && path[1] == 0)
    path = "";

  return path;
}

/* We need to find any explicitly given emulation in order to initialize the
   state that's needed by the lex&yacc argument parser (parse_args).  */

static char *
get_emulation (int argc, char **argv)
{
  char *emulation;
  int i;

  emulation = getenv (EMULATION_ENVIRON);
  if (emulation == NULL)
    emulation = DEFAULT_EMULATION;

  for (i = 1; i < argc; i++)
    {
      if (startswith (argv[i], "-m"))
	{
	  if (argv[i][2] == '\0')
	    {
	      /* -m EMUL */
	      if (i < argc - 1)
		{
		  emulation = argv[i + 1];
		  i++;
		}
	      else
		einfo (_("%F%P: missing argument to -m\n"));
	    }
	  else if (strcmp (argv[i], "-mips1") == 0
		   || strcmp (argv[i], "-mips2") == 0
		   || strcmp (argv[i], "-mips3") == 0
		   || strcmp (argv[i], "-mips4") == 0
		   || strcmp (argv[i], "-mips5") == 0
		   || strcmp (argv[i], "-mips32") == 0
		   || strcmp (argv[i], "-mips32r2") == 0
		   || strcmp (argv[i], "-mips32r3") == 0
		   || strcmp (argv[i], "-mips32r5") == 0
		   || strcmp (argv[i], "-mips32r6") == 0
		   || strcmp (argv[i], "-mips64") == 0
		   || strcmp (argv[i], "-mips64r2") == 0
		   || strcmp (argv[i], "-mips64r3") == 0
		   || strcmp (argv[i], "-mips64r5") == 0
		   || strcmp (argv[i], "-mips64r6") == 0)
	    {
	      /* FIXME: The arguments -mips1, -mips2, -mips3, etc. are
		 passed to the linker by some MIPS compilers.  They
		 generally tell the linker to use a slightly different
		 library path.  Perhaps someday these should be
		 implemented as emulations; until then, we just ignore
		 the arguments and hope that nobody ever creates
		 emulations named ips1, ips2 or ips3.  */
	    }
	  else if (strcmp (argv[i], "-m486") == 0)
	    {
	      /* FIXME: The argument -m486 is passed to the linker on
		 some Linux systems.  Hope that nobody creates an
		 emulation named 486.  */
	    }
	  else
	    {
	      /* -mEMUL */
	      emulation = &argv[i][2];
	    }
	}
    }

  return emulation;
}

void
add_ysym (const char *name)
{
  if (link_info.notice_hash == NULL)
    {
      link_info.notice_hash
	= (struct bfd_hash_table *) xmalloc (sizeof (struct bfd_hash_table));
      if (!bfd_hash_table_init_n (link_info.notice_hash,
				  bfd_hash_newfunc,
				  sizeof (struct bfd_hash_entry),
				  61))
	einfo (_("%F%P: bfd_hash_table_init failed: %E\n"));
    }

  if (bfd_hash_lookup (link_info.notice_hash, name, true, true) == NULL)
    einfo (_("%F%P: bfd_hash_lookup failed: %E\n"));
}

void
add_ignoresym (struct bfd_link_info *info, const char *name)
{
  if (info->ignore_hash == NULL)
    {
      info->ignore_hash = xmalloc (sizeof (struct bfd_hash_table));
      if (!bfd_hash_table_init_n (info->ignore_hash,
				  bfd_hash_newfunc,
				  sizeof (struct bfd_hash_entry),
				  61))
	einfo (_("%F%P: bfd_hash_table_init failed: %E\n"));
    }

  if (bfd_hash_lookup (info->ignore_hash, name, true, true) == NULL)
    einfo (_("%F%P: bfd_hash_lookup failed: %E\n"));
}

/* Record a symbol to be wrapped, from the --wrap option.  */

void
add_wrap (const char *name)
{
  if (link_info.wrap_hash == NULL)
    {
      link_info.wrap_hash
	= (struct bfd_hash_table *) xmalloc (sizeof (struct bfd_hash_table));
      if (!bfd_hash_table_init_n (link_info.wrap_hash,
				  bfd_hash_newfunc,
				  sizeof (struct bfd_hash_entry),
				  61))
	einfo (_("%F%P: bfd_hash_table_init failed: %E\n"));
    }

  if (bfd_hash_lookup (link_info.wrap_hash, name, true, true) == NULL)
    einfo (_("%F%P: bfd_hash_lookup failed: %E\n"));
}

/* Handle the -retain-symbols-file option.  */

void
add_keepsyms_file (const char *filename)
{
  FILE *file;
  char *buf;
  size_t bufsize;
  int c;

  if (link_info.strip == strip_some)
    einfo (_("%X%P: error: duplicate retain-symbols-file\n"));

  file = fopen (filename, "r");
  if (file == NULL)
    {
      bfd_set_error (bfd_error_system_call);
      einfo ("%X%P: %s: %E\n", filename);
      return;
    }

  link_info.keep_hash = (struct bfd_hash_table *)
      xmalloc (sizeof (struct bfd_hash_table));
  if (!bfd_hash_table_init (link_info.keep_hash, bfd_hash_newfunc,
			    sizeof (struct bfd_hash_entry)))
    einfo (_("%F%P: bfd_hash_table_init failed: %E\n"));

  bufsize = 100;
  buf = (char *) xmalloc (bufsize);

  c = getc (file);
  while (c != EOF)
    {
      while (ISSPACE (c))
	c = getc (file);

      if (c != EOF)
	{
	  size_t len = 0;

	  while (!ISSPACE (c) && c != EOF)
	    {
	      buf[len] = c;
	      ++len;
	      if (len >= bufsize)
		{
		  bufsize *= 2;
		  buf = (char *) xrealloc (buf, bufsize);
		}
	      c = getc (file);
	    }

	  buf[len] = '\0';

	  if (bfd_hash_lookup (link_info.keep_hash, buf, true, true) == NULL)
	    einfo (_("%F%P: bfd_hash_lookup for insertion failed: %E\n"));
	}
    }

  if (link_info.strip != strip_none)
    einfo (_("%P: `-retain-symbols-file' overrides `-s' and `-S'\n"));

  free (buf);
  link_info.strip = strip_some;
  fclose (file);
}

/* Callbacks from the BFD linker routines.  */

/* This is called when BFD has decided to include an archive member in
   a link.  */

static bool
add_archive_element (struct bfd_link_info *info,
		     bfd *abfd,
		     const char *name,
		     bfd **subsbfd ATTRIBUTE_UNUSED)
{
  lang_input_statement_type *input;
  lang_input_statement_type *parent;
  lang_input_statement_type orig_input;

  input = (lang_input_statement_type *)
      xcalloc (1, sizeof (lang_input_statement_type));
  input->header.type = lang_input_statement_enum;
  input->filename = bfd_get_filename (abfd);
  input->local_sym_name = bfd_get_filename (abfd);
  input->the_bfd = abfd;

  /* Save the original data for trace files/tries below, as plugins
     (if enabled) may possibly alter it to point to a replacement
     BFD, but we still want to output the original BFD filename.  */
  orig_input = *input;
#if BFD_SUPPORTS_PLUGINS
  if (link_info.lto_plugin_active)
    {
      /* We must offer this archive member to the plugins to claim.  */
      plugin_maybe_claim (input);
      if (input->flags.claimed)
	{
	  if (no_more_claiming)
	    {
	      /* Don't claim new IR symbols after all IR symbols have
		 been claimed.  */
	      if (verbose)
		info_msg ("%pI: no new IR symbols to claim\n",
			  &orig_input);
	      input->flags.claimed = 0;
	      return false;
	    }
	  input->flags.claim_archive = true;
	  *subsbfd = input->the_bfd;
	}
    }
#endif /* BFD_SUPPORTS_PLUGINS */

  if (link_info.input_bfds_tail == &input->the_bfd->link.next
      || input->the_bfd->link.next != NULL)
    {
      /* We have already loaded this element, and are attempting to
	 load it again.  This can happen when the archive map doesn't
	 match actual symbols defined by the element.  */
      free (input);
      bfd_set_error (bfd_error_malformed_archive);
      return false;
    }

  /* Set the file_chain pointer of archives to the last element loaded
     from the archive.  See ldlang.c:find_rescan_insertion.  */
  parent = bfd_usrdata (abfd->my_archive);
  if (parent != NULL && !parent->flags.reload)
    parent->next = input;

  ldlang_add_file (input);

  if (config.map_file != NULL)
    {
      static bool header_printed;
      struct bfd_link_hash_entry *h;
      bfd *from;
      int len;

      h = bfd_link_hash_lookup (info->hash, name, false, false, true);
      if (h == NULL
	  && info->pei386_auto_import
	  && startswith (name, "__imp_"))
	h = bfd_link_hash_lookup (info->hash, name + 6, false, false, true);

      if (h == NULL)
	from = NULL;
      else
	{
	  switch (h->type)
	    {
	    default:
	      from = NULL;
	      break;

	    case bfd_link_hash_defined:
	    case bfd_link_hash_defweak:
	      from = h->u.def.section->owner;
	      break;

	    case bfd_link_hash_undefined:
	    case bfd_link_hash_undefweak:
	      from = h->u.undef.abfd;
	      break;

	    case bfd_link_hash_common:
	      from = h->u.c.p->section->owner;
	      break;
	    }
	}

      if (!header_printed)
	{
	  minfo (_("Archive member included to satisfy reference by file (symbol)\n\n"));
	  header_printed = true;
	}

      if (abfd->my_archive == NULL
	  || bfd_is_thin_archive (abfd->my_archive))
	{
	  minfo ("%s", bfd_get_filename (abfd));
	  len = strlen (bfd_get_filename (abfd));
	}
      else
	{
	  minfo ("%s(%s)", bfd_get_filename (abfd->my_archive),
		 bfd_get_filename (abfd));
	  len = (strlen (bfd_get_filename (abfd->my_archive))
		 + strlen (bfd_get_filename (abfd))
		 + 2);
	}

      if (len >= 29)
	{
	  print_nl ();
	  len = 0;
	}
      while (len < 30)
	{
	  print_space ();
	  ++len;
	}

      if (from != NULL)
	minfo ("%pB ", from);
      if (h != NULL)
	minfo ("(%pT)\n", h->root.string);
      else
	minfo ("(%s)\n", name);
    }

  if (verbose
      || trace_files > 1
      || (trace_files && bfd_is_thin_archive (orig_input.the_bfd->my_archive)))
    info_msg ("%pI\n", &orig_input);
  return true;
}

/* This is called when BFD has discovered a symbol which is defined
   multiple times.  */

static void
multiple_definition (struct bfd_link_info *info,
		     struct bfd_link_hash_entry *h,
		     bfd *nbfd,
		     asection *nsec,
		     bfd_vma nval)
{
  const char *name;
  bfd *obfd;
  asection *osec;
  bfd_vma oval;

  if (info->allow_multiple_definition)
    return;

  switch (h->type)
    {
    case bfd_link_hash_defined:
      osec = h->u.def.section;
      oval = h->u.def.value;
      obfd = h->u.def.section->owner;
      break;
    case bfd_link_hash_indirect:
      osec = bfd_ind_section_ptr;
      oval = 0;
      obfd = NULL;
      break;
    default:
      abort ();
    }

  /* Ignore a redefinition of an absolute symbol to the
     same value; it's harmless.  */
  if (h->type == bfd_link_hash_defined
      && bfd_is_abs_section (osec)
      && bfd_is_abs_section (nsec)
      && nval == oval)
    return;

  /* If either section has the output_section field set to
     bfd_abs_section_ptr, it means that the section is being
     discarded, and this is not really a multiple definition at all.
     FIXME: It would be cleaner to somehow ignore symbols defined in
     sections which are being discarded.  */
  if (!info->prohibit_multiple_definition_absolute
      && ((osec->output_section != NULL
	   && ! bfd_is_abs_section (osec)
	   && bfd_is_abs_section (osec->output_section))
	  || (nsec->output_section != NULL
	      && !bfd_is_abs_section (nsec)
	      && bfd_is_abs_section (nsec->output_section))))
    return;

  name = h->root.string;
  if (nbfd == NULL)
    {
      nbfd = obfd;
      nsec = osec;
      nval = oval;
      obfd = NULL;
    }
  if (info->warn_multiple_definition)
    einfo (_("%P: %C: warning: multiple definition of `%pT'"),
	   nbfd, nsec, nval, name);
  else
    einfo (_("%X%P: %C: multiple definition of `%pT'"),
	   nbfd, nsec, nval, name);
  if (obfd != NULL)
    einfo (_("; %D: first defined here"), obfd, osec, oval);
  einfo ("\n");

  if (RELAXATION_ENABLED_BY_USER)
    {
      einfo (_("%P: disabling relaxation; it will not work with multiple definitions\n"));
      DISABLE_RELAXATION;
    }
}

/* This is called when there is a definition of a common symbol, or
   when a common symbol is found for a symbol that is already defined,
   or when two common symbols are found.  We only do something if
   -warn-common was used.  */

static void
multiple_common (struct bfd_link_info *info ATTRIBUTE_UNUSED,
		 struct bfd_link_hash_entry *h,
		 bfd *nbfd,
		 enum bfd_link_hash_type ntype,
		 bfd_vma nsize)
{
  const char *name;
  bfd *obfd;
  enum bfd_link_hash_type otype;
  bfd_vma osize;

  if (!config.warn_common)
    return;

  name = h->root.string;
  otype = h->type;
  if (otype == bfd_link_hash_common)
    {
      obfd = h->u.c.p->section->owner;
      osize = h->u.c.size;
    }
  else if (otype == bfd_link_hash_defined
	   || otype == bfd_link_hash_defweak)
    {
      obfd = h->u.def.section->owner;
      osize = 0;
    }
  else
    {
      /* FIXME: It would nice if we could report the BFD which defined
	 an indirect symbol, but we don't have anywhere to store the
	 information.  */
      obfd = NULL;
      osize = 0;
    }

  if (ntype == bfd_link_hash_defined
      || ntype == bfd_link_hash_defweak
      || ntype == bfd_link_hash_indirect)
    {
      ASSERT (otype == bfd_link_hash_common);
      if (obfd != NULL)
	einfo (_("%P: %pB: warning: definition of `%pT' overriding common"
		 " from %pB\n"),
	       nbfd, name, obfd);
      else
	einfo (_("%P: %pB: warning: definition of `%pT' overriding common\n"),
	       nbfd, name);
    }
  else if (otype == bfd_link_hash_defined
	   || otype == bfd_link_hash_defweak
	   || otype == bfd_link_hash_indirect)
    {
      ASSERT (ntype == bfd_link_hash_common);
      if (obfd != NULL)
	einfo (_("%P: %pB: warning: common of `%pT' overridden by definition"
		 " from %pB\n"),
	       nbfd, name, obfd);
      else
	einfo (_("%P: %pB: warning: common of `%pT' overridden by definition\n"),
	       nbfd, name);
    }
  else
    {
      ASSERT (otype == bfd_link_hash_common && ntype == bfd_link_hash_common);
      if (osize > nsize)
	{
	  if (obfd != NULL)
	    einfo (_("%P: %pB: warning: common of `%pT' overridden"
		     " by larger common from %pB\n"),
		   nbfd, name, obfd);
	  else
	    einfo (_("%P: %pB: warning: common of `%pT' overridden"
		     " by larger common\n"),
		   nbfd, name);
	}
      else if (nsize > osize)
	{
	  if (obfd != NULL)
	    einfo (_("%P: %pB: warning: common of `%pT' overriding"
		     " smaller common from %pB\n"),
		   nbfd, name, obfd);
	  else
	    einfo (_("%P: %pB: warning: common of `%pT' overriding"
		     " smaller common\n"),
		   nbfd, name);
	}
      else
	{
	  if (obfd != NULL)
	    einfo (_("%P: %pB and %pB: warning: multiple common of `%pT'\n"),
		   nbfd, obfd, name);
	  else
	    einfo (_("%P: %pB: warning: multiple common of `%pT'\n"),
		   nbfd, name);
	}
    }
}

/* This is called when BFD has discovered a set element.  H is the
   entry in the linker hash table for the set.  SECTION and VALUE
   represent a value which should be added to the set.  */

static void
add_to_set (struct bfd_link_info *info ATTRIBUTE_UNUSED,
	    struct bfd_link_hash_entry *h,
	    bfd_reloc_code_real_type reloc,
	    bfd *abfd,
	    asection *section,
	    bfd_vma value)
{
  if (config.warn_constructors)
    einfo (_("%P: warning: global constructor %s used\n"),
	   h->root.string);

  if (!config.build_constructors)
    return;

  ldctor_add_set_entry (h, reloc, NULL, section, value);

  if (h->type == bfd_link_hash_new)
    {
      h->type = bfd_link_hash_undefined;
      h->u.undef.abfd = abfd;
      /* We don't call bfd_link_add_undef to add this to the list of
	 undefined symbols because we are going to define it
	 ourselves.  */
    }
}

/* This is called when BFD has discovered a constructor.  This is only
   called for some object file formats--those which do not handle
   constructors in some more clever fashion.  This is similar to
   adding an element to a set, but less general.  */

static void
constructor_callback (struct bfd_link_info *info,
		      bool constructor,
		      const char *name,
		      bfd *abfd,
		      asection *section,
		      bfd_vma value)
{
  char *s;
  struct bfd_link_hash_entry *h;
  char set_name[1 + sizeof "__CTOR_LIST__"];

  if (config.warn_constructors)
    einfo (_("%P: warning: global constructor %s used\n"), name);

  if (!config.build_constructors)
    return;

  /* Ensure that BFD_RELOC_CTOR exists now, so that we can give a
     useful error message.  */
  if (bfd_reloc_type_lookup (info->output_bfd, BFD_RELOC_CTOR) == NULL
      && (bfd_link_relocatable (info)
	  || bfd_reloc_type_lookup (abfd, BFD_RELOC_CTOR) == NULL))
    einfo (_("%F%P: BFD backend error: BFD_RELOC_CTOR unsupported\n"));

  s = set_name;
  if (bfd_get_symbol_leading_char (abfd) != '\0')
    *s++ = bfd_get_symbol_leading_char (abfd);
  if (constructor)
    strcpy (s, "__CTOR_LIST__");
  else
    strcpy (s, "__DTOR_LIST__");

  h = bfd_link_hash_lookup (info->hash, set_name, true, true, true);
  if (h == (struct bfd_link_hash_entry *) NULL)
    einfo (_("%F%P: bfd_link_hash_lookup failed: %E\n"));
  if (h->type == bfd_link_hash_new)
    {
      h->type = bfd_link_hash_undefined;
      h->u.undef.abfd = abfd;
      /* We don't call bfd_link_add_undef to add this to the list of
	 undefined symbols because we are going to define it
	 ourselves.  */
    }

  ldctor_add_set_entry (h, BFD_RELOC_CTOR, name, section, value);
}

/* A structure used by warning_callback to pass information through
   bfd_map_over_sections.  */

struct warning_callback_info
{
  bool found;
  const char *warning;
  const char *symbol;
  asymbol **asymbols;
};

/* Look through the relocs to see if we can find a plausible address
   for SYMBOL in ABFD.  Return TRUE if found.  Otherwise return FALSE.  */

static bool
symbol_warning (const char *warning, const char *symbol, bfd *abfd)
{
  struct warning_callback_info cinfo;

  if (!bfd_generic_link_read_symbols (abfd))
    einfo (_("%F%P: %pB: could not read symbols: %E\n"), abfd);

  cinfo.found = false;
  cinfo.warning = warning;
  cinfo.symbol = symbol;
  cinfo.asymbols = bfd_get_outsymbols (abfd);
  bfd_map_over_sections (abfd, warning_find_reloc, &cinfo);
  return cinfo.found;
}

/* This is called when there is a reference to a warning symbol.  */

static void
warning_callback (struct bfd_link_info *info ATTRIBUTE_UNUSED,
		  const char *warning,
		  const char *symbol,
		  bfd *abfd,
		  asection *section,
		  bfd_vma address)
{
  /* This is a hack to support warn_multiple_gp.  FIXME: This should
     have a cleaner interface, but what?  */
  if (!config.warn_multiple_gp
      && strcmp (warning, "using multiple gp values") == 0)
    return;

  if (section != NULL)
    einfo ("%P: %C: %s%s\n", abfd, section, address, _("warning: "), warning);
  else if (abfd == NULL)
    einfo ("%P: %s%s\n", _("warning: "), warning);
  else if (symbol == NULL)
    einfo ("%P: %pB: %s%s\n", abfd, _("warning: "), warning);
  else if (!symbol_warning (warning, symbol, abfd))
    {
      bfd *b;
      /* Search all input files for a reference to SYMBOL.  */
      for (b = info->input_bfds; b; b = b->link.next)
	if (b != abfd && symbol_warning (warning, symbol, b))
	  return;
      einfo ("%P: %pB: %s%s\n", abfd, _("warning: "), warning);
    }
}

/* This is called by warning_callback for each section.  It checks the
   relocs of the section to see if it can find a reference to the
   symbol which triggered the warning.  If it can, it uses the reloc
   to give an error message with a file and line number.  */

static void
warning_find_reloc (bfd *abfd, asection *sec, void *iarg)
{
  struct warning_callback_info *info = (struct warning_callback_info *) iarg;
  long relsize;
  arelent **relpp;
  long relcount;
  arelent **p, **pend;

  if (info->found)
    return;

  relsize = bfd_get_reloc_upper_bound (abfd, sec);
  if (relsize < 0)
    einfo (_("%F%P: %pB: could not read relocs: %E\n"), abfd);
  if (relsize == 0)
    return;

  relpp = (arelent **) xmalloc (relsize);
  relcount = bfd_canonicalize_reloc (abfd, sec, relpp, info->asymbols);
  if (relcount < 0)
    einfo (_("%F%P: %pB: could not read relocs: %E\n"), abfd);

  p = relpp;
  pend = p + relcount;
  for (; p < pend && *p != NULL; p++)
    {
      arelent *q = *p;

      if (q->sym_ptr_ptr != NULL
	  && *q->sym_ptr_ptr != NULL
	  && strcmp (bfd_asymbol_name (*q->sym_ptr_ptr), info->symbol) == 0)
	{
	  /* We found a reloc for the symbol we are looking for.  */
	  einfo ("%P: %C: %s%s\n", abfd, sec, q->address, _("warning: "),
		 info->warning);
	  info->found = true;
	  break;
	}
    }

  free (relpp);
}

#if SUPPORT_ERROR_HANDLING_SCRIPT
char * error_handling_script = NULL;
#endif

/* This is called when an undefined symbol is found.  */

static void
undefined_symbol (struct bfd_link_info *info,
		  const char *name,
		  bfd *abfd,
		  asection *section,
		  bfd_vma address,
		  bool error)
{
  static char *error_name;
  static unsigned int error_count;

#define MAX_ERRORS_IN_A_ROW 5

  if (info->ignore_hash != NULL
      && bfd_hash_lookup (info->ignore_hash, name, false, false) != NULL)
    return;

  if (config.warn_once)
    {
      /* Only warn once about a particular undefined symbol.  */
      add_ignoresym (info, name);
    }

  /* We never print more than a reasonable number of errors in a row
     for a single symbol.  */
  if (error_name != NULL
      && strcmp (name, error_name) == 0)
    ++error_count;
  else
    {
      error_count = 0;
      free (error_name);
      error_name = xstrdup (name);
    }

#if SUPPORT_ERROR_HANDLING_SCRIPT
  if (error_handling_script != NULL
      && error_count < MAX_ERRORS_IN_A_ROW)
    {
      char *        argv[4];
      const char *  res;
      int           status, err;

      argv[0] = error_handling_script;
      argv[1] = "undefined-symbol";
      argv[2] = (char *) name;
      argv[3] = NULL;
      
      if (verbose)
	einfo (_("%P: About to run error handling script '%s' with arguments: '%s' '%s'\n"),
	       argv[0], argv[1], argv[2]);

      res = pex_one (PEX_SEARCH, error_handling_script, argv,
		     N_("error handling script"),
		     NULL /* Send stdout to random, temp file.  */,
		     NULL /* Write to stderr.  */,
		     &status, &err);
      if (res != NULL)
	{
	  einfo (_("%P: Failed to run error handling script '%s', reason: "),
		 error_handling_script);
	  /* FIXME: We assume here that errrno == err.  */
	  perror (res);
	}
      /* We ignore the return status of the script and
	 carry on to issue the normal error message.  */
    }
#endif /* SUPPORT_ERROR_HANDLING_SCRIPT */
  
  if (section != NULL)
    {
      if (error_count < MAX_ERRORS_IN_A_ROW)
	{
	  if (error)
	    einfo (_("%X%P: %C: undefined reference to `%pT'\n"),
		   abfd, section, address, name);
	  else
	    einfo (_("%P: %C: warning: undefined reference to `%pT'\n"),
		   abfd, section, address, name);
	}
      else if (error_count == MAX_ERRORS_IN_A_ROW)
	{
	  if (error)
	    einfo (_("%X%P: %D: more undefined references to `%pT' follow\n"),
		   abfd, section, address, name);
	  else
	    einfo (_("%P: %D: warning: more undefined references to `%pT' follow\n"),
		   abfd, section, address, name);
	}
      else if (error)
	einfo ("%X");
    }
  else
    {
      if (error_count < MAX_ERRORS_IN_A_ROW)
	{
	  if (error)
	    einfo (_("%X%P: %pB: undefined reference to `%pT'\n"),
		   abfd, name);
	  else
	    einfo (_("%P: %pB: warning: undefined reference to `%pT'\n"),
		   abfd, name);
	}
      else if (error_count == MAX_ERRORS_IN_A_ROW)
	{
	  if (error)
	    einfo (_("%X%P: %pB: more undefined references to `%pT' follow\n"),
		   abfd, name);
	  else
	    einfo (_("%P: %pB: warning: more undefined references to `%pT' follow\n"),
		   abfd, name);
	}
      else if (error)
	einfo ("%X");
    }
}

/* Counter to limit the number of relocation overflow error messages
   to print.  Errors are printed as it is decremented.  When it's
   called and the counter is zero, a final message is printed
   indicating more relocations were omitted.  When it gets to -1, no
   such errors are printed.  If it's initially set to a value less
   than -1, all such errors will be printed (--verbose does this).  */

int overflow_cutoff_limit = 10;

/* This is called when a reloc overflows.  */

static void
reloc_overflow (struct bfd_link_info *info,
		struct bfd_link_hash_entry *entry,
		const char *name,
		const char *reloc_name,
		bfd_vma addend,
		bfd *abfd,
		asection *section,
		bfd_vma address)
{
  if (overflow_cutoff_limit == -1)
    return;

  einfo ("%X%H:", abfd, section, address);

  if (overflow_cutoff_limit >= 0
      && overflow_cutoff_limit-- == 0)
    {
      einfo (_(" additional relocation overflows omitted from the output\n"));
      return;
    }

  if (entry)
    {
      while (entry->type == bfd_link_hash_indirect
	     || entry->type == bfd_link_hash_warning)
	entry = entry->u.i.link;
      switch (entry->type)
	{
	case bfd_link_hash_undefined:
	case bfd_link_hash_undefweak:
	  einfo (_(" relocation truncated to fit: "
		   "%s against undefined symbol `%pT'"),
		 reloc_name, entry->root.string);
	  break;
	case bfd_link_hash_defined:
	case bfd_link_hash_defweak:
	  einfo (_(" relocation truncated to fit: "
		   "%s against symbol `%pT' defined in %pA section in %pB"),
		 reloc_name, entry->root.string,
		 entry->u.def.section,
		 entry->u.def.section == bfd_abs_section_ptr
		 ? info->output_bfd : entry->u.def.section->owner);
	  break;
	default:
	  abort ();
	  break;
	}
    }
  else
    einfo (_(" relocation truncated to fit: %s against `%pT'"),
	   reloc_name, name);
  if (addend != 0)
    einfo ("+%v", addend);
  einfo ("\n");
}

/* This is called when a dangerous relocation is made.  */

static void
reloc_dangerous (struct bfd_link_info *info ATTRIBUTE_UNUSED,
		 const char *message,
		 bfd *abfd,
		 asection *section,
		 bfd_vma address)
{
  einfo (_("%X%H: dangerous relocation: %s\n"),
	 abfd, section, address, message);
}

/* This is called when a reloc is being generated attached to a symbol
   that is not being output.  */

static void
unattached_reloc (struct bfd_link_info *info ATTRIBUTE_UNUSED,
		  const char *name,
		  bfd *abfd,
		  asection *section,
		  bfd_vma address)
{
  einfo (_("%X%H: reloc refers to symbol `%pT' which is not being output\n"),
	 abfd, section, address, name);
}

/* This is called if link_info.notice_all is set, or when a symbol in
   link_info.notice_hash is found.  Symbols are put in notice_hash
   using the -y option, while notice_all is set if the --cref option
   has been supplied, or if there are any NOCROSSREFS sections in the
   linker script; and if plugins are active, since they need to monitor
   all references from non-IR files.  */

static bool
notice (struct bfd_link_info *info,
	struct bfd_link_hash_entry *h,
	struct bfd_link_hash_entry *inh ATTRIBUTE_UNUSED,
	bfd *abfd,
	asection *section,
	bfd_vma value,
	flagword flags ATTRIBUTE_UNUSED)
{
  const char *name;

  if (h == NULL)
    {
      if (command_line.cref || nocrossref_list != NULL)
	return handle_asneeded_cref (abfd, (enum notice_asneeded_action) value);
      return true;
    }

  name = h->root.string;
  if (info->notice_hash != NULL
      && bfd_hash_lookup (info->notice_hash, name, false, false) != NULL)
    {
      if (bfd_is_und_section (section))
	einfo (_("%P: %pB: reference to %s\n"), abfd, name);
      else
	einfo (_("%P: %pB: definition of %s\n"), abfd, name);
    }

  if (command_line.cref || nocrossref_list != NULL)
    add_cref (name, abfd, section, value);

  return true;
}
